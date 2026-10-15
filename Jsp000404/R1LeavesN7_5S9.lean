import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4900 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4901 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4903 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4904 | h4904
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4905 | h4905
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4906 | h4906
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4907 | h4907
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4908 | h4908
          · linarith only [h0, h1, h4901, h4903, h4908, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4910 | h4910
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4911 | h4911
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4912 | h4912
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4913 | h4913
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4914 | h4914
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4915 | h4915
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4916 | h4916
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4917 | h4917
                          · linarith only [h0, h1, h4908, h4910, h4917, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1, h4908, h4910, h4914, h4917, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1, h4908, h4916, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h4908, h4915, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4922 | h4922
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4923 | h4923
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4924 | h4924
                          · linarith only [h4910, h4914, h4924, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4926 | h4926
                            · linarith only [h4910, h4914, h4922, h4926, hlam]
                            · rcases h0bigk with h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c | h4928c
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4903, h4907, h4910, h4914, h4922, hc34, hlam, hphi, ht0b, ht45, ht5b, p4928_1, u0elo0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h1, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h1, h4907, h4908, h4910, h4914, h4922, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4928_1]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h1, h4907, h4908, h4910, h4914, h4922, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4928_1]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h0, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4901, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4907, h4910, h4914, h4922, hc34, hlam, hphi, ht0b, ht45, ht5b, p4928_1, u0elo1]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h0, h1, h4907, h4908, h4910, h4914, h4922, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4928_1]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4928_1, u0elo2]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4903, h4922, hc34, hlam, hphi, ht0b, ht45, ht5b, p4928_1, u0elo2]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4907, h4910, h4914, h4922, hc34, hlam, hphi, ht0b, ht45, ht5b, p4928_1, u0elo2]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4907, h4910, h4914, h4922, hc34, hlam, hphi, ht0b, ht45, ht5b, p4928_1, u0elo2]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4899, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4903, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4905, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h0, h1, h4903, h4907, h4908, h4910, h4914, h4922, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4928_1]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4900, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4904, hlam, p4928_1]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4906, hlam, p4928_0]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [h4907, hlam, p4928_1]
                              · have p4928_0 := h4928c.1
                                have p4928_1 := h4928c.2.1
                                have p4928_2 := h4928c.2.2.1
                                have p4928_3 := h4928c.2.2.2
                                linarith only [hlam, p4928_0]
                        · linarith only [h0, h1, h4908, h4910, h4922, h4923, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h4903, h4907, h4908, h4914, h4922, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h4910, h4913, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h4910, h4912, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h0, h4904, h4910, h4911, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h4903, h4908, h4910, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4960 | h4960
          · linarith only [h0, h4901, h4960, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4962 | h4962
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4963 | h4963
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4964 | h4964
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4965 | h4965
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4966 | h4966
                    · linarith only [h1, h4899, h4907, h4960, h4966, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4968 | h4968
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4969 | h4969
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4970 | h4970
                          · linarith only [h4903, h4907, h4970, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4972 | h4972
                            · linarith only [h0, h1, h4907, h4960, h4963, h4968, h4970, h4972, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases h0bigk with h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c | h4974c
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h1, h4960, hc02, hc23, hlam, hphi, p4974_1]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h1, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                rcases p4974_3 (m.d 0 1) (by simp) with h4978 | h4978
                                · rcases p4974_3 (m.d 0 2) (by simp) with h4979 | h4979
                                  · linarith only [h0, h4979, hlam]
                                  · linarith only [h4903, h4979, hlam]
                                · linarith only [h4899, h4978, hlam]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                rcases p4974_3 (m.d 0 1) (by simp) with h4983 | h4983
                                · rcases p4974_3 (m.d 0 2) (by simp) with h4984 | h4984
                                  · linarith only [h0, h4984, hlam]
                                  · linarith only [h4904, h4984, hlam]
                                · linarith only [h4900, h4983, hlam]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h0, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4901, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                rcases p4974_3 (m.d 0 1) (by simp) with h4991 | h4991
                                · rcases p4974_3 (m.d 0 2) (by simp) with h4992 | h4992
                                  · rcases p4974_3 (m.d 0 3) (by simp) with h4993 | h4993
                                    · rcases p4974_3 (m.d 0 4) (by simp) with h4994 | h4994
                                      · linarith only [h4903, h4994, hlam]
                                      · rcases p4974_3 (m.d 0 5) (by simp) with h4996 | h4996
                                        · linarith only [h4904, h4996, hlam]
                                        · linarith only [h4907, h4996, hlam]
                                    · linarith only [h4905, h4993, hlam]
                                  · linarith only [h4903, h4992, hlam]
                                · linarith only [h4899, h4991, hlam]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                rcases p4974_3 (m.d 0 1) (by simp) with h5002 | h5002
                                · rcases p4974_3 (m.d 0 2) (by simp) with h5003 | h5003
                                  · rcases p4974_3 (m.d 0 3) (by simp) with h5004 | h5004
                                    · rcases p4974_3 (m.d 0 4) (by simp) with h5005 | h5005
                                      · linarith only [h4903, h5005, hlam]
                                      · rcases p4974_3 (m.d 0 5) (by simp) with h5007 | h5007
                                        · linarith only [h4904, h5007, hlam]
                                        · rcases h0emin with h5009 | h5009 | h5009 | h5009 | h5009
                                          · rcases h1bigk with h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h1, h4960, hc12, hc23, hlam, hphi, p5010_1]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h1, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              rcases p5010_3 (m.d 0 1) (by simp) with h5014 | h5014
                                              · rcases p5010_3 (m.d 1 2) (by simp) with h5015 | h5015
                                                · linarith only [h0, h5015, hlam]
                                                · linarith only [h4962, h5015, hlam]
                                              · linarith only [h5014, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              rcases p5010_3 (m.d 0 1) (by simp) with h5019 | h5019
                                              · rcases p5010_3 (m.d 1 2) (by simp) with h5020 | h5020
                                                · linarith only [h0, h5020, hlam]
                                                · linarith only [h4963, h5020, hlam]
                                              · linarith only [h5019, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h0, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4960, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h0, h1, h4960, h4962, h4968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5010_1]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h0, h1, h4960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5010_1]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4960, h5009, hc23, hlam, ht01, ht12, p5010_1]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              rcases p5010_3 (m.d 0 1) (by simp) with h5030 | h5030
                                              · linarith only [h1, h5030, hlam]
                                              · linarith only [h0, h5030, hlam]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h0, h1, h4899, h4907, hlam, p4974_1, p5010_2]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h0, h1, h4900, hlam, p4974_1, p5010_2]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4899, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4962, hlam, p5010_1]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4964, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4966, hlam, p5010_1]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4900, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4963, hlam, p5010_1]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h4965, hlam, p5010_0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [h0, h4900, h4962, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p4974_1, p5010_1, u0elo0]
                                            · have p5010_0 := h5010c.1
                                              have p5010_1 := h5010c.2.1
                                              have p5010_2 := h5010c.2.2.1
                                              have p5010_3 := h5010c.2.2.2
                                              linarith only [hlam, p5010_0]
                                          · rcases h1bigk with h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c | h5046c
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h1, h4960, hc12, hc23, hlam, hphi, p5046_1]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h1, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              rcases p5046_3 (m.d 0 1) (by simp) with h5050 | h5050
                                              · rcases p5046_3 (m.d 1 2) (by simp) with h5051 | h5051
                                                · linarith only [h0, h5051, hlam]
                                                · linarith only [h4962, h5051, hlam]
                                              · linarith only [h5050, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              rcases p5046_3 (m.d 0 1) (by simp) with h5055 | h5055
                                              · rcases p5046_3 (m.d 1 2) (by simp) with h5056 | h5056
                                                · linarith only [h0, h5056, hlam]
                                                · linarith only [h4963, h5056, hlam]
                                              · linarith only [h5055, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h0, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4960, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h0, h1, h4960, h4962, h4968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5046_1]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h0, h1, h4960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5046_1]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h0, h4960, h5009, hc23, hlam, ht01, ht12, p5046_1]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              rcases p5046_3 (m.d 0 1) (by simp) with h5066 | h5066
                                              · linarith only [h1, h5066, hlam]
                                              · linarith only [h0, h5066, hlam]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h0, h1, h4899, h4907, hlam, p4974_1, p5046_2]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h0, h1, h4900, hlam, p4974_1, p5046_2]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4899, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4962, hlam, p5046_1]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4964, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4966, hlam, p5046_1]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4900, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4963, hlam, p5046_1]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h4965, hlam, p5046_0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [h0, h4900, h4962, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p4974_1, p5046_1, u0elo0]
                                            · have p5046_0 := h5046c.1
                                              have p5046_1 := h5046c.2.1
                                              have p5046_2 := h5046c.2.2.1
                                              have p5046_3 := h5046c.2.2.2
                                              linarith only [hlam, p5046_0]
                                          · rcases h1bigk with h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c | h5082c
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h1, h4960, hc12, hc23, hlam, hphi, p5082_1]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h1, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              rcases p5082_3 (m.d 0 1) (by simp) with h5086 | h5086
                                              · rcases p5082_3 (m.d 1 2) (by simp) with h5087 | h5087
                                                · linarith only [h0, h5087, hlam]
                                                · linarith only [h4962, h5087, hlam]
                                              · linarith only [h5086, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              rcases p5082_3 (m.d 0 1) (by simp) with h5091 | h5091
                                              · rcases p5082_3 (m.d 1 2) (by simp) with h5092 | h5092
                                                · linarith only [h0, h5092, hlam]
                                                · linarith only [h4963, h5092, hlam]
                                              · linarith only [h5091, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h0, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4960, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h0, h1, h4960, h4962, h4968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5082_1]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h0, h1, h4960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5082_1]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h0, h4960, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4974_1, p5082_1]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              rcases p5082_3 (m.d 0 1) (by simp) with h5102 | h5102
                                              · linarith only [h1, h5102, hlam]
                                              · linarith only [h0, h5102, hlam]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h0, h1, h4899, h4907, hlam, p4974_1, p5082_2]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h0, h1, h4900, hlam, p4974_1, p5082_2]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4899, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4962, hlam, p5082_1]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4964, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4966, hlam, p5082_1]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4900, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4963, hlam, p5082_1]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h4965, hlam, p5082_0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [h0, h4900, h4962, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p4974_1, p5082_1, u0elo0]
                                            · have p5082_0 := h5082c.1
                                              have p5082_1 := h5082c.2.1
                                              have p5082_2 := h5082c.2.2.1
                                              have p5082_3 := h5082c.2.2.2
                                              linarith only [hlam, p5082_0]
                                          · linarith only [h0, h1, h4907, h5009, hc13, hlam, ht01, p4974_1]
                                          · linarith only [h0, h1, h5009, hc13, hlam, ht01, p4974_1]
                                    · linarith only [h4906, h5004, hlam]
                                  · linarith only [h4904, h5003, hlam]
                                · linarith only [h4900, h5002, hlam]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4974_1, u0elo2]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4903, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p4974_1, u0elo2]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                rcases p4974_3 (m.d 0 1) (by simp) with h5126 | h5126
                                · linarith only [h1, h5126, hlam]
                                · linarith only [h4899, h5126, hlam]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                rcases p4974_3 (m.d 0 1) (by simp) with h5129 | h5129
                                · linarith only [h1, h5129, hlam]
                                · linarith only [h4900, h5129, hlam]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4899, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4903, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4905, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4907, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4900, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4904, hlam, p4974_1]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [h4906, hlam, p4974_0]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                rcases p4974_3 (m.d 0 1) (by simp) with h5140 | h5140
                                · rcases p4974_3 (m.d 0 2) (by simp) with h5141 | h5141
                                  · rcases p4974_3 (m.d 0 3) (by simp) with h5142 | h5142
                                    · rcases p4974_3 (m.d 0 4) (by simp) with h5143 | h5143
                                      · linarith only [h4907, h5143, hlam]
                                      · rcases p4974_3 (m.d 0 5) (by simp) with h5145 | h5145
                                        · rcases h0emin with h5146 | h5146 | h5146 | h5146 | h5146
                                          · rcases h1bigk with h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c | h5147c
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h1, h4960, h4963, h4968, h4970, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5147_1]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h1, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              rcases p5147_3 (m.d 0 1) (by simp) with h5151 | h5151
                                              · rcases p5147_3 (m.d 1 2) (by simp) with h5152 | h5152
                                                · linarith only [h0, h5152, hlam]
                                                · linarith only [h4962, h5152, hlam]
                                              · linarith only [h5151, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              rcases p5147_3 (m.d 0 1) (by simp) with h5156 | h5156
                                              · rcases p5147_3 (m.d 1 2) (by simp) with h5157 | h5157
                                                · linarith only [h0, h5157, hlam]
                                                · linarith only [h4963, h5157, hlam]
                                              · linarith only [h5156, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h0, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4960, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h0, h1, h4960, h4962, h4968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5147_1]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h0, h1, h4960, h4963, h4968, h4970, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5147_1]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4960, h5146, hc23, hlam, ht01, ht12, p5147_1]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              rcases p5147_3 (m.d 0 1) (by simp) with h5167 | h5167
                                              · linarith only [h1, h5167, hlam]
                                              · linarith only [h0, h5167, hlam]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h0, h1, h4899, h4904, hlam, p4974_1, p5147_2]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              rcases p5147_3 (m.d 0 1) (by simp) with h5172 | h5172
                                              · linarith only [h1, h5172, hlam]
                                              · linarith only [h4900, h5172, hlam]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4899, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4962, hlam, p5147_1]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4964, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4966, hlam, p5147_1]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4900, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4963, hlam, p5147_1]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4965, hlam, p5147_0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [h4900, h4962, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p5147_1, u0elo0]
                                            · have p5147_0 := h5147c.1
                                              have p5147_1 := h5147c.2.1
                                              have p5147_2 := h5147c.2.2.1
                                              have p5147_3 := h5147c.2.2.2
                                              linarith only [hlam, p5147_0]
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
                                              linarith only [h1, h4960, hc12, hc23, hlam, hphi, p5185_1]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h1, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              rcases p5185_3 (m.d 0 1) (by simp) with h5189 | h5189
                                              · rcases p5185_3 (m.d 1 2) (by simp) with h5190 | h5190
                                                · linarith only [h0, h5190, hlam]
                                                · linarith only [h4962, h5190, hlam]
                                              · linarith only [h5189, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              rcases p5185_3 (m.d 0 1) (by simp) with h5194 | h5194
                                              · rcases p5185_3 (m.d 1 2) (by simp) with h5195 | h5195
                                                · linarith only [h0, h5195, hlam]
                                                · linarith only [h4963, h5195, hlam]
                                              · linarith only [h5194, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h0, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4960, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h0, h1, h4960, h4962, h4968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5185_1]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h0, h1, h4960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5185_1]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h0, h4960, hc12, hc23, hlam, hphi, p5185_1]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              rcases p5185_3 (m.d 0 1) (by simp) with h5205 | h5205
                                              · linarith only [h1, h5205, hlam]
                                              · linarith only [h0, h5205, hlam]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h0, h1, h4899, h4904, hlam, p4974_1, p5185_2]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              rcases p5185_3 (m.d 0 1) (by simp) with h5210 | h5210
                                              · linarith only [h1, h5210, hlam]
                                              · linarith only [h4900, h5210, hlam]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4899, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4962, hlam, p5185_1]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4964, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4966, hlam, p5185_1]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4900, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4963, hlam, p5185_1]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4965, hlam, p5185_0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [h4900, h4962, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p5185_1, u0elo0]
                                            · have p5185_0 := h5185c.1
                                              have p5185_1 := h5185c.2.1
                                              have p5185_2 := h5185c.2.2.1
                                              have p5185_3 := h5185c.2.2.2
                                              linarith only [hlam, p5185_0]
                                          · rcases h1bigk with h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c | h5223c
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h1, h4960, hc12, hc23, hlam, hphi, p5223_1]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h1, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              rcases p5223_3 (m.d 0 1) (by simp) with h5227 | h5227
                                              · rcases p5223_3 (m.d 1 2) (by simp) with h5228 | h5228
                                                · linarith only [h0, h5228, hlam]
                                                · linarith only [h4962, h5228, hlam]
                                              · linarith only [h5227, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              rcases p5223_3 (m.d 0 1) (by simp) with h5232 | h5232
                                              · rcases p5223_3 (m.d 1 2) (by simp) with h5233 | h5233
                                                · linarith only [h0, h5233, hlam]
                                                · linarith only [h4963, h5233, hlam]
                                              · linarith only [h5232, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h0, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4960, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h0, h1, h4960, h4962, h4968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5223_1]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h0, h1, h4960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5223_1]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h0, h4960, hc12, hc23, hlam, hphi, p5223_1]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              rcases p5223_3 (m.d 0 1) (by simp) with h5243 | h5243
                                              · linarith only [h1, h5243, hlam]
                                              · linarith only [h0, h5243, hlam]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h0, h1, h4899, h4904, hlam, p4974_1, p5223_2]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              rcases p5223_3 (m.d 0 1) (by simp) with h5248 | h5248
                                              · linarith only [h1, h5248, hlam]
                                              · linarith only [h4900, h5248, hlam]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4899, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4962, hlam, p5223_1]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4964, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4966, hlam, p5223_1]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4900, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4963, hlam, p5223_1]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4965, hlam, p5223_0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [h4900, h4962, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p5223_1, u0elo0]
                                            · have p5223_0 := h5223c.1
                                              have p5223_1 := h5223c.2.1
                                              have p5223_2 := h5223c.2.2.1
                                              have p5223_3 := h5223c.2.2.2
                                              linarith only [hlam, p5223_0]
                                          · linarith only [h4904, h5146, hlam, p4974_1, u0elo1]
                                          · rcases h1bigk with h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h1, h4960, h4963, h4968, h4970, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5262_1]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h1, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              rcases p5262_3 (m.d 0 1) (by simp) with h5266 | h5266
                                              · rcases p5262_3 (m.d 1 2) (by simp) with h5267 | h5267
                                                · linarith only [h0, h5267, hlam]
                                                · linarith only [h4962, h5267, hlam]
                                              · linarith only [h5266, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              rcases p5262_3 (m.d 0 1) (by simp) with h5271 | h5271
                                              · rcases p5262_3 (m.d 1 2) (by simp) with h5272 | h5272
                                                · linarith only [h0, h5272, hlam]
                                                · linarith only [h4963, h5272, hlam]
                                              · linarith only [h5271, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h0, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4960, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h0, h1, h4960, h4962, h4968, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5262_1]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h0, h1, h4960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5262_1]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h0, h4904, h4960, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4974_1, p5262_1]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              rcases p5262_3 (m.d 0 1) (by simp) with h5282 | h5282
                                              · linarith only [h1, h5282, hlam]
                                              · linarith only [h0, h5282, hlam]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h0, h1, h4899, h4904, hlam, p4974_1, p5262_2]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              rcases p5262_3 (m.d 0 1) (by simp) with h5287 | h5287
                                              · linarith only [h1, h5287, hlam]
                                              · linarith only [h4900, h5287, hlam]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4899, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4962, hlam, p5262_1]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4964, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4966, hlam, p5262_1]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4900, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4963, hlam, p5262_1]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4965, hlam, p5262_0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [h4900, h4962, h4968, hc34, hlam, hphi, ht0b, ht45, ht5b, p5262_1, u0elo0]
                                            · have p5262_0 := h5262c.1
                                              have p5262_1 := h5262c.2.1
                                              have p5262_2 := h5262c.2.2.1
                                              have p5262_3 := h5262c.2.2.2
                                              linarith only [hlam, p5262_0]
                                        · linarith only [h4907, h5145, hlam]
                                    · linarith only [h4905, h5142, hlam]
                                  · linarith only [h4903, h5141, hlam]
                                · linarith only [h4899, h5140, hlam]
                              · have p4974_0 := h4974c.1
                                have p4974_1 := h4974c.2.1
                                have p4974_2 := h4974c.2.2.1
                                have p4974_3 := h4974c.2.2.2
                                linarith only [hlam, p4974_0]
                        · linarith only [h0, h1, h4960, h4969, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h4960, h4962, h4968, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h4962, h4965, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h4962, h4964, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h0, h4904, h4962, h4963, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h4903, h4960, h4962, hc12, hc23, hlam, hphi]
      · linarith only [h0, h1, h4904, h4906, hlam]
    · linarith only [h1, h4899, h4905, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5313 | h5313
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5314 | h5314
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5315 | h5315
        · linarith only [h4903, h4904, h5315, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5317 | h5317
          · linarith only [h0, h4901, h5317, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5319 | h5319
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5320 | h5320
              · linarith only [h0, h4904, h5320, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5322 | h5322
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5323 | h5323
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5324 | h5324
                    · linarith only [h1, h4899, h5315, h5317, h5324, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5326 | h5326
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5327 | h5327
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5328 | h5328
                          · linarith only [h0, h5315, h5319, h5328, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5330 | h5330
                            · linarith only [h0, h1, h4899, h4904, h5317, h5319, h5326, h5328, h5330, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c | h5332c
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h0, h1, h5317, h5319, h5326, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5332_1]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h1, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                rcases p5332_3 (m.d 0 1) (by simp) with h5336 | h5336
                                · rcases p5332_3 (m.d 0 2) (by simp) with h5337 | h5337
                                  · linarith only [h0, h5337, hlam]
                                  · linarith only [h4903, h5337, hlam]
                                · linarith only [h4899, h5336, hlam]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h0, h1, h4904, h5317, h5319, h5326, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5332_1]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h0, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h4901, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h4899, h4904, h5328, hc14, hc45, hlam, hphi, p5332_1]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h4904, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h0, h5319, h5326, hc34, hlam, hphi, ht0b, ht45, ht5b, p5332_1, u0elo2]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h0, h5319, h5326, hc34, hlam, hphi, ht0b, ht45, ht5b, p5332_1, u0elo2]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                rcases p5332_3 (m.d 0 1) (by simp) with h5350 | h5350
                                · linarith only [h1, h5350, hlam]
                                · linarith only [h4899, h5350, hlam]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h0, h4904, h5319, h5326, hc34, hlam, hphi, ht0b, ht45, ht5b, p5332_1, u0elo2]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h4899, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h4903, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h5313, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h5315, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h4900, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h0, h5319, h5326, hc34, hlam, hphi, ht0b, ht45, ht5b, p5332_1, u0elo4]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [h5314, hlam, p5332_0]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                rcases p5332_3 (m.d 0 1) (by simp) with h5362 | h5362
                                · rcases p5332_3 (m.d 0 2) (by simp) with h5363 | h5363
                                  · linarith only [h4904, h5363, hlam]
                                  · linarith only [h4903, h5363, hlam]
                                · linarith only [h4899, h5362, hlam]
                              · have p5332_0 := h5332c.1
                                have p5332_1 := h5332c.2.1
                                have p5332_2 := h5332c.2.2.1
                                have p5332_3 := h5332c.2.2.2
                                linarith only [hlam, p5332_0]
                        · linarith only [h0, h1, h5317, h5319, h5326, h5327, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1, h4900, h5317, h5319, h5320, h5326, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h1, h4900, h5319, h5320, h5323, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1, h4900, h5319, h5320, h5322, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h0, h1, h4903, h5317, h5319, hc12, hc23, hlam, hphi]
      · linarith only [h1, h4900, h5314, hlam]
    · linarith only [h1, h4899, h5313, hlam]

end R2N4
