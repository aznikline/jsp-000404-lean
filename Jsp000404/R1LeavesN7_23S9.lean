import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5788000 in
set_option maxHeartbeats 5788000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s19_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3219 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg3221 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg3223 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg3225 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3226 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg3227 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg3228 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg3229 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg3230 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg3231 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg3232 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg3233 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg3234 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg3235 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg3236 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h3237 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h4686 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h4905 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have h0 := hg0
  have h3219 := hg3219
  have h3221 := hg3221
  have h3223 := hg3223
  have h3225 := hg3225
  have h3226 := hg3226
  have h3227 := hg3227
  have h3228 := hg3228
  have h3229 := hg3229
  have h3230 := hg3230
  have h3231 := hg3231
  have h3232 := hg3232
  have h3233 := hg3233
  have h3234 := hg3234
  have h3235 := hg3235
  have h3236 := hg3236
  rcases m.htr 3 4 5 (by decide) (by decide) with h4906 | h4906
  · rcases h2bigk with h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c | h4907c
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h0, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h4910 | h4910
      · rcases p4907_3 (m.d 1 2) (by simp) with h4911 | h4911
        · rcases p4907_3 (m.d 2 3) (by simp) with h4912 | h4912
          · linarith only [h4912, hlam, p4907_0]
          · rcases p4907_3 (m.d 2 4) (by simp) with h4914 | h4914
            · linarith only [h3226, h4914, hlam]
            · linarith only [h3237, h4914, hlam]
        · linarith only [h3231, h4911, hlam]
      · linarith only [h4910, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h4919 | h4919
      · rcases p4907_3 (m.d 1 2) (by simp) with h4920 | h4920
        · rcases p4907_3 (m.d 2 3) (by simp) with h4921 | h4921
          · linarith only [h3225, h4921, hlam]
          · rcases p4907_3 (m.d 2 4) (by simp) with h4923 | h4923
            · linarith only [h4923, hlam, p4907_0]
            · rcases p4907_3 (m.d 2 5) (by simp) with h4925 | h4925
              · linarith only [h3227, h4925, hlam]
              · rcases h2emax with h4927 | h4927 | h4927 | h4927 | h4927
                · linarith only [h0, h4927, hlam, ht12, u1ehi0]
                · linarith only [h4927, hlam, ht12, u1ehi1]
                · rcases h4bigk with h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c | h4930c
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3221, hlam, p4930_1]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    rcases p4930_3 (m.d 0 4) (by simp) with h4933 | h4933
                    · rcases p4930_3 (m.d 1 4) (by simp) with h4934 | h4934
                      · rcases p4930_3 (m.d 2 4) (by simp) with h4935 | h4935
                        · linarith only [h3226, h4935, hlam]
                        · rcases p4930_3 (m.d 3 4) (by simp) with h4937 | h4937
                          · linarith only [h3228, h4937, hlam]
                          · linarith only [h3237, h4937, hlam]
                      · linarith only [h3232, h4934, hlam]
                    · linarith only [h3226, h4933, hlam]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    rcases p4930_3 (m.d 0 4) (by simp) with h4942 | h4942
                    · rcases p4930_3 (m.d 1 4) (by simp) with h4943 | h4943
                      · rcases p4930_3 (m.d 2 4) (by simp) with h4944 | h4944
                        · linarith only [h3226, h4944, hlam]
                        · rcases p4930_3 (m.d 3 4) (by simp) with h4946 | h4946
                          · linarith only [h3228, h4946, hlam]
                          · rcases p4930_3 (m.d 4 5) (by simp) with h4948 | h4948
                            · linarith only [h3230, h4948, hlam]
                            · rcases h5bigk with h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c | h4950c
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [hlam, p4950_0]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3223, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                rcases p4950_3 (m.d 0 5) (by simp) with h4953 | h4953
                                · rcases p4950_3 (m.d 1 5) (by simp) with h4954 | h4954
                                  · rcases p4950_3 (m.d 2 5) (by simp) with h4955 | h4955
                                    · linarith only [h3227, h4955, hlam]
                                    · rcases p4950_3 (m.d 3 5) (by simp) with h4957 | h4957
                                      · linarith only [h3229, h4957, hlam]
                                      · linarith only [h4686, h4957, hlam]
                                  · linarith only [h3233, h4954, hlam]
                                · linarith only [h3227, h4953, hlam]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3225, h3228, h3230, h4686, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                rcases p4950_3 (m.d 0 5) (by simp) with h4963 | h4963
                                · rcases p4950_3 (m.d 1 5) (by simp) with h4964 | h4964
                                  · rcases p4950_3 (m.d 2 5) (by simp) with h4965 | h4965
                                    · linarith only [h3227, h4965, hlam]
                                    · linarith only [h4905, h4965, hlam]
                                  · linarith only [h3236, h4964, hlam]
                                · linarith only [h3230, h4963, hlam]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3223, hc15, hlam, hphi, p4950_1, u1ehi0]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [hlam, p4950_0]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                rcases p4950_3 (m.d 0 5) (by simp) with h4972 | h4972
                                · linarith only [h3223, h4972, hlam]
                                · linarith only [h3227, h4972, hlam]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3231, h3234, h3236, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                rcases p4950_3 (m.d 0 5) (by simp) with h4976 | h4976
                                · linarith only [h3223, h4976, hlam]
                                · linarith only [h3230, h4976, hlam]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3227, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3233, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [hlam, p4950_0]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h4686, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h0, h3227, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3229, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3235, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h0, h3225, h3228, h4906, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [hlam, p4950_0]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h0, h3225, h3228, h4906, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4930_1, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3230, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h3236, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h4905, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [h4906, hlam, p4950_1]
                              · have p4950_0 := h4950c.1
                                have p4950_1 := h4950c.2.1
                                have p4950_2 := h4950c.2.2.1
                                have p4950_3 := h4950c.2.2.2
                                linarith only [hlam, p4950_0]
                      · linarith only [h3234, h4943, hlam]
                    · linarith only [h3228, h4942, hlam]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    rcases p4930_3 (m.d 0 4) (by simp) with h4996 | h4996
                    · rcases p4930_3 (m.d 1 4) (by simp) with h4997 | h4997
                      · rcases p4930_3 (m.d 2 4) (by simp) with h4998 | h4998
                        · linarith only [h3226, h4998, hlam]
                        · linarith only [h4905, h4998, hlam]
                      · linarith only [h3236, h4997, hlam]
                    · linarith only [h4996, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p4930_1, u1ehi0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    rcases p4930_3 (m.d 0 4) (by simp) with h5005 | h5005
                    · linarith only [h3221, h5005, hlam]
                    · linarith only [h3226, h5005, hlam]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    rcases p4930_3 (m.d 0 4) (by simp) with h5008 | h5008
                    · linarith only [h3221, h5008, hlam]
                    · linarith only [h3228, h5008, hlam]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    rcases p4930_3 (m.d 0 4) (by simp) with h5011 | h5011
                    · linarith only [h3221, h5011, hlam]
                    · linarith only [h3230, h5011, hlam]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3226, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3232, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3237, hlam, p4930_1]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4907_1, p4930_1]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3228, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3234, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3225, h3228, hlam, p4907_2, p4930_1]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    rcases p4930_3 (m.d 0 4) (by simp) with h5023 | h5023
                    · rcases p4930_3 (m.d 1 4) (by simp) with h5024 | h5024
                      · rcases p4930_3 (m.d 2 4) (by simp) with h5025 | h5025
                        · linarith only [h3237, h5025, hlam]
                        · linarith only [h4905, h5025, hlam]
                      · linarith only [h3236, h5024, hlam]
                    · linarith only [h3230, h5023, hlam]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3230, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h3236, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h4905, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [h4906, hlam, p4930_0]
                  · have p4930_0 := h4930c.1
                    have p4930_1 := h4930c.2.1
                    have p4930_2 := h4930c.2.2.1
                    have p4930_3 := h4930c.2.2.2
                    linarith only [hlam, p4930_0]
                · rcases h4bigk with h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c | h5035c
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3221, hlam, p5035_1]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    rcases p5035_3 (m.d 0 4) (by simp) with h5038 | h5038
                    · rcases p5035_3 (m.d 1 4) (by simp) with h5039 | h5039
                      · rcases p5035_3 (m.d 2 4) (by simp) with h5040 | h5040
                        · linarith only [h3226, h5040, hlam]
                        · rcases p5035_3 (m.d 3 4) (by simp) with h5042 | h5042
                          · linarith only [h3228, h5042, hlam]
                          · linarith only [h3237, h5042, hlam]
                      · linarith only [h3232, h5039, hlam]
                    · linarith only [h3226, h5038, hlam]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    rcases p5035_3 (m.d 0 4) (by simp) with h5047 | h5047
                    · rcases p5035_3 (m.d 1 4) (by simp) with h5048 | h5048
                      · rcases p5035_3 (m.d 2 4) (by simp) with h5049 | h5049
                        · linarith only [h3226, h5049, hlam]
                        · rcases p5035_3 (m.d 3 4) (by simp) with h5051 | h5051
                          · linarith only [h3228, h5051, hlam]
                          · rcases p5035_3 (m.d 4 5) (by simp) with h5053 | h5053
                            · linarith only [h3230, h5053, hlam]
                            · rcases h5bigk with h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [hlam, p5055_0]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3223, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                rcases p5055_3 (m.d 0 5) (by simp) with h5058 | h5058
                                · rcases p5055_3 (m.d 1 5) (by simp) with h5059 | h5059
                                  · rcases p5055_3 (m.d 2 5) (by simp) with h5060 | h5060
                                    · linarith only [h3227, h5060, hlam]
                                    · rcases p5055_3 (m.d 3 5) (by simp) with h5062 | h5062
                                      · linarith only [h3229, h5062, hlam]
                                      · linarith only [h4686, h5062, hlam]
                                  · linarith only [h3233, h5059, hlam]
                                · linarith only [h3227, h5058, hlam]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3223, h3231, h3234, h3236, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                rcases p5055_3 (m.d 0 5) (by simp) with h5068 | h5068
                                · rcases p5055_3 (m.d 1 5) (by simp) with h5069 | h5069
                                  · rcases p5055_3 (m.d 2 5) (by simp) with h5070 | h5070
                                    · linarith only [h3227, h5070, hlam]
                                    · linarith only [h4905, h5070, hlam]
                                  · linarith only [h3236, h5069, hlam]
                                · linarith only [h3230, h5068, hlam]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p5055_1, u1ehi0]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [hlam, p5055_0]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                rcases p5055_3 (m.d 0 5) (by simp) with h5077 | h5077
                                · linarith only [h3223, h5077, hlam]
                                · linarith only [h3227, h5077, hlam]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3231, h3234, h3236, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                rcases p5055_3 (m.d 0 5) (by simp) with h5081 | h5081
                                · linarith only [h3223, h5081, hlam]
                                · linarith only [h3230, h5081, hlam]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3227, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3233, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [hlam, p5055_0]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h4686, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h0, h3227, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3229, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3235, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h0, h3225, h3229, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [hlam, p5055_0]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3221, h3231, h3234, h4906, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5035_1, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3230, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h3236, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h4905, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [h4906, hlam, p5055_1]
                              · have p5055_0 := h5055c.1
                                have p5055_1 := h5055c.2.1
                                have p5055_2 := h5055c.2.2.1
                                have p5055_3 := h5055c.2.2.2
                                linarith only [hlam, p5055_0]
                      · linarith only [h3234, h5048, hlam]
                    · linarith only [h3228, h5047, hlam]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    rcases p5035_3 (m.d 0 4) (by simp) with h5101 | h5101
                    · rcases p5035_3 (m.d 1 4) (by simp) with h5102 | h5102
                      · rcases p5035_3 (m.d 2 4) (by simp) with h5103 | h5103
                        · linarith only [h3226, h5103, hlam]
                        · linarith only [h4905, h5103, hlam]
                      · linarith only [h3236, h5102, hlam]
                    · linarith only [h5101, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5035_1, u1ehi0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    rcases p5035_3 (m.d 0 4) (by simp) with h5110 | h5110
                    · linarith only [h3221, h5110, hlam]
                    · linarith only [h3226, h5110, hlam]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    rcases p5035_3 (m.d 0 4) (by simp) with h5113 | h5113
                    · linarith only [h3221, h5113, hlam]
                    · linarith only [h3228, h5113, hlam]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    rcases p5035_3 (m.d 0 4) (by simp) with h5116 | h5116
                    · linarith only [h3221, h5116, hlam]
                    · linarith only [h3230, h5116, hlam]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3226, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3232, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3237, hlam, p5035_1]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4907_1, p5035_1]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3228, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3234, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3225, h3228, hlam, p4907_2, p5035_1]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    rcases p5035_3 (m.d 0 4) (by simp) with h5128 | h5128
                    · rcases p5035_3 (m.d 1 4) (by simp) with h5129 | h5129
                      · rcases p5035_3 (m.d 2 4) (by simp) with h5130 | h5130
                        · linarith only [h3237, h5130, hlam]
                        · linarith only [h4905, h5130, hlam]
                      · linarith only [h3236, h5129, hlam]
                    · linarith only [h3230, h5128, hlam]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3230, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h3236, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h4905, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [h4906, hlam, p5035_0]
                  · have p5035_0 := h5035c.1
                    have p5035_1 := h5035c.2.1
                    have p5035_2 := h5035c.2.2.1
                    have p5035_3 := h5035c.2.2.2
                    linarith only [hlam, p5035_0]
                · rcases h4bigk with h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3221, hlam, p5140_1]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    rcases p5140_3 (m.d 0 4) (by simp) with h5143 | h5143
                    · rcases p5140_3 (m.d 1 4) (by simp) with h5144 | h5144
                      · rcases p5140_3 (m.d 2 4) (by simp) with h5145 | h5145
                        · linarith only [h3226, h5145, hlam]
                        · rcases p5140_3 (m.d 3 4) (by simp) with h5147 | h5147
                          · linarith only [h3228, h5147, hlam]
                          · linarith only [h3237, h5147, hlam]
                      · linarith only [h3232, h5144, hlam]
                    · linarith only [h3226, h5143, hlam]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    rcases p5140_3 (m.d 0 4) (by simp) with h5152 | h5152
                    · rcases p5140_3 (m.d 1 4) (by simp) with h5153 | h5153
                      · rcases p5140_3 (m.d 2 4) (by simp) with h5154 | h5154
                        · linarith only [h3226, h5154, hlam]
                        · rcases p5140_3 (m.d 3 4) (by simp) with h5156 | h5156
                          · linarith only [h3228, h5156, hlam]
                          · rcases p5140_3 (m.d 4 5) (by simp) with h5158 | h5158
                            · linarith only [h3230, h5158, hlam]
                            · rcases h5bigk with h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [hlam, p5160_0]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3223, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                rcases p5160_3 (m.d 0 5) (by simp) with h5163 | h5163
                                · rcases p5160_3 (m.d 1 5) (by simp) with h5164 | h5164
                                  · rcases p5160_3 (m.d 2 5) (by simp) with h5165 | h5165
                                    · linarith only [h3227, h5165, hlam]
                                    · rcases p5160_3 (m.d 3 5) (by simp) with h5167 | h5167
                                      · linarith only [h3229, h5167, hlam]
                                      · linarith only [h4686, h5167, hlam]
                                  · linarith only [h3233, h5164, hlam]
                                · linarith only [h3227, h5163, hlam]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3223, h3231, h3234, h3236, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                rcases p5160_3 (m.d 0 5) (by simp) with h5173 | h5173
                                · rcases p5160_3 (m.d 1 5) (by simp) with h5174 | h5174
                                  · rcases p5160_3 (m.d 2 5) (by simp) with h5175 | h5175
                                    · linarith only [h3227, h5175, hlam]
                                    · linarith only [h4905, h5175, hlam]
                                  · linarith only [h3236, h5174, hlam]
                                · linarith only [h3230, h5173, hlam]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p5160_1, u1ehi0]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [hlam, p5160_0]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                rcases p5160_3 (m.d 0 5) (by simp) with h5182 | h5182
                                · linarith only [h3223, h5182, hlam]
                                · linarith only [h3227, h5182, hlam]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3231, h3234, h3236, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                rcases p5160_3 (m.d 0 5) (by simp) with h5186 | h5186
                                · linarith only [h3223, h5186, hlam]
                                · linarith only [h3230, h5186, hlam]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3227, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3233, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [hlam, p5160_0]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h4686, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h0, h3227, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3229, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3235, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h0, h3225, h3229, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [hlam, p5160_0]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3221, h3231, h3234, h4906, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5140_1, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3230, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h3236, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h4905, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [h4906, hlam, p5160_1]
                              · have p5160_0 := h5160c.1
                                have p5160_1 := h5160c.2.1
                                have p5160_2 := h5160c.2.2.1
                                have p5160_3 := h5160c.2.2.2
                                linarith only [hlam, p5160_0]
                      · linarith only [h3234, h5153, hlam]
                    · linarith only [h3228, h5152, hlam]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    rcases p5140_3 (m.d 0 4) (by simp) with h5206 | h5206
                    · rcases p5140_3 (m.d 1 4) (by simp) with h5207 | h5207
                      · rcases p5140_3 (m.d 2 4) (by simp) with h5208 | h5208
                        · linarith only [h3226, h5208, hlam]
                        · linarith only [h4905, h5208, hlam]
                      · linarith only [h3236, h5207, hlam]
                    · linarith only [h5206, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5140_1, u1ehi0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    rcases p5140_3 (m.d 0 4) (by simp) with h5215 | h5215
                    · linarith only [h3221, h5215, hlam]
                    · linarith only [h3226, h5215, hlam]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    rcases p5140_3 (m.d 0 4) (by simp) with h5218 | h5218
                    · linarith only [h3221, h5218, hlam]
                    · linarith only [h3228, h5218, hlam]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    rcases p5140_3 (m.d 0 4) (by simp) with h5221 | h5221
                    · linarith only [h3221, h5221, hlam]
                    · linarith only [h3230, h5221, hlam]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3226, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3232, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3237, hlam, p5140_1]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4907_1, p5140_1]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3228, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3234, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3225, h3228, hlam, p4907_2, p5140_1]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    rcases p5140_3 (m.d 0 4) (by simp) with h5233 | h5233
                    · rcases p5140_3 (m.d 1 4) (by simp) with h5234 | h5234
                      · rcases p5140_3 (m.d 2 4) (by simp) with h5235 | h5235
                        · linarith only [h3237, h5235, hlam]
                        · linarith only [h4905, h5235, hlam]
                      · linarith only [h3236, h5234, hlam]
                    · linarith only [h3230, h5233, hlam]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3230, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h3236, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h4905, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [h4906, hlam, p5140_0]
                  · have p5140_0 := h5140c.1
                    have p5140_1 := h5140c.2.1
                    have p5140_2 := h5140c.2.2.1
                    have p5140_3 := h5140c.2.2.2
                    linarith only [hlam, p5140_0]
        · linarith only [h3232, h4920, hlam]
      · linarith only [h4919, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h5247 | h5247
      · rcases p4907_3 (m.d 1 2) (by simp) with h5248 | h5248
        · rcases p4907_3 (m.d 2 3) (by simp) with h5249 | h5249
          · linarith only [h3225, h5249, hlam]
          · rcases p4907_3 (m.d 2 4) (by simp) with h5251 | h5251
            · linarith only [h3226, h5251, hlam]
            · linarith only [h4905, h5251, hlam]
        · linarith only [h3233, h5248, hlam]
      · linarith only [h5247, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h0, hc12, hlam, hphi, p4907_1, u1ehi0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h5258 | h5258
      · linarith only [h0, h5258, hlam]
      · linarith only [h3225, h5258, hlam]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h5261 | h5261
      · linarith only [h0, h5261, hlam]
      · linarith only [h3226, h5261, hlam]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h5264 | h5264
      · linarith only [h0, h5264, hlam]
      · linarith only [h3227, h5264, hlam]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h3225, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h3231, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h3237, hlam, p4907_1]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h4686, hlam, p4907_1]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h3226, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h3232, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h5274 | h5274
      · rcases p4907_3 (m.d 1 2) (by simp) with h5275 | h5275
        · rcases p4907_3 (m.d 2 3) (by simp) with h5276 | h5276
          · linarith only [h3237, h5276, hlam]
          · rcases p4907_3 (m.d 2 4) (by simp) with h5278 | h5278
            · rcases p4907_3 (m.d 2 5) (by simp) with h5279 | h5279
              · linarith only [h4905, h5279, hlam]
              · linarith only [h4686, h5279, hlam]
            · linarith only [h3237, h5278, hlam]
        · linarith only [h3231, h5275, hlam]
      · linarith only [h3225, h5274, hlam]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h5286 | h5286
      · rcases p4907_3 (m.d 1 2) (by simp) with h5287 | h5287
        · rcases p4907_3 (m.d 2 3) (by simp) with h5288 | h5288
          · linarith only [h3237, h5288, hlam]
          · rcases p4907_3 (m.d 2 4) (by simp) with h5290 | h5290
            · rcases p4907_3 (m.d 2 5) (by simp) with h5291 | h5291
              · linarith only [h4905, h5291, hlam]
              · rcases h2emax with h5293 | h5293 | h5293 | h5293 | h5293
                · linarith only [h3225, h3228, h3237, h4686, h5293, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4907_1]
                · linarith only [h5293, hlam, ht12, u1ehi1]
                · rcases h4bigk with h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c | h5296c
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3221, hlam, p5296_1]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h4686, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4907_1, p5296_1]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3237, h4686, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4907_1, p5296_1]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    rcases p5296_3 (m.d 0 4) (by simp) with h5301 | h5301
                    · rcases p5296_3 (m.d 1 4) (by simp) with h5302 | h5302
                      · rcases p5296_3 (m.d 2 4) (by simp) with h5303 | h5303
                        · linarith only [h3226, h5303, hlam]
                        · linarith only [h4905, h5303, hlam]
                      · linarith only [h3236, h5302, hlam]
                    · linarith only [h5301, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5296_1, u1ehi0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3231, h3234, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5296_1]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3231, h3234, h3237, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5296_1]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    rcases p5296_3 (m.d 0 4) (by simp) with h5312 | h5312
                    · linarith only [h3221, h5312, hlam]
                    · linarith only [h3230, h5312, hlam]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3226, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3232, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3237, hlam, p5296_1]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    rcases p5296_3 (m.d 0 4) (by simp) with h5319 | h5319
                    · rcases p5296_3 (m.d 1 4) (by simp) with h5320 | h5320
                      · rcases p5296_3 (m.d 2 4) (by simp) with h5321 | h5321
                        · rcases p5296_3 (m.d 3 4) (by simp) with h5322 | h5322
                          · rcases p5296_3 (m.d 4 5) (by simp) with h5323 | h5323
                            · linarith only [h5323, hlam, p5296_0]
                            · rcases h5bigk with h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c | h5325c
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [hlam, p5325_0]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3223, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                rcases p5325_3 (m.d 0 5) (by simp) with h5328 | h5328
                                · rcases p5325_3 (m.d 1 5) (by simp) with h5329 | h5329
                                  · rcases p5325_3 (m.d 2 5) (by simp) with h5330 | h5330
                                    · linarith only [h3227, h5330, hlam]
                                    · rcases p5325_3 (m.d 3 5) (by simp) with h5332 | h5332
                                      · linarith only [h3229, h5332, hlam]
                                      · linarith only [h4686, h5332, hlam]
                                  · linarith only [h3233, h5329, hlam]
                                · linarith only [h3227, h5328, hlam]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3225, h3228, h3230, h4686, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                rcases p5325_3 (m.d 0 5) (by simp) with h5338 | h5338
                                · rcases p5325_3 (m.d 1 5) (by simp) with h5339 | h5339
                                  · rcases p5325_3 (m.d 2 5) (by simp) with h5340 | h5340
                                    · linarith only [h3227, h5340, hlam]
                                    · linarith only [h4905, h5340, hlam]
                                  · linarith only [h3236, h5339, hlam]
                                · linarith only [h3230, h5338, hlam]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3223, hc15, hlam, hphi, p5325_1, u1ehi0]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [hlam, p5325_0]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                rcases p5325_3 (m.d 0 5) (by simp) with h5347 | h5347
                                · linarith only [h3223, h5347, hlam]
                                · linarith only [h3227, h5347, hlam]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3236, h4686, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                rcases p5325_3 (m.d 0 5) (by simp) with h5351 | h5351
                                · linarith only [h3223, h5351, hlam]
                                · linarith only [h3230, h5351, hlam]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3227, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3233, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [hlam, p5325_0]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h4686, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4907_1, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3229, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3235, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h0, h3225, h3229, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [hlam, p5325_0]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h0, h3225, h3228, h4906, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3230, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h3236, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h4905, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [h4906, hlam, p5325_1]
                              · have p5325_0 := h5325c.1
                                have p5325_1 := h5325c.2.1
                                have p5325_2 := h5325c.2.2.1
                                have p5325_3 := h5325c.2.2.2
                                linarith only [hlam, p5325_0]
                          · linarith only [h4906, h5322, hlam]
                        · linarith only [h5321, hlam, p5296_0]
                      · linarith only [h3236, h5320, hlam]
                    · linarith only [h3230, h5319, hlam]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3228, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3234, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h0, h3225, h3228, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5296_1]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    rcases p5296_3 (m.d 0 4) (by simp) with h5377 | h5377
                    · rcases p5296_3 (m.d 1 4) (by simp) with h5378 | h5378
                      · rcases p5296_3 (m.d 2 4) (by simp) with h5379 | h5379
                        · linarith only [h3237, h5379, hlam]
                        · linarith only [h4905, h5379, hlam]
                      · linarith only [h3236, h5378, hlam]
                    · linarith only [h3230, h5377, hlam]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3230, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h3236, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h4905, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [h4906, hlam, p5296_0]
                  · have p5296_0 := h5296c.1
                    have p5296_1 := h5296c.2.1
                    have p5296_2 := h5296c.2.2.1
                    have p5296_3 := h5296c.2.2.2
                    linarith only [hlam, p5296_0]
                · linarith only [h4686, h5293, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4907_1]
                · rcases h4bigk with h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c | h5390c
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3221, hlam, p5390_1]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h0, h3225, h3228, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5390_1]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h0, h3225, h3228, h3237, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5390_1]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    rcases p5390_3 (m.d 0 4) (by simp) with h5395 | h5395
                    · rcases p5390_3 (m.d 1 4) (by simp) with h5396 | h5396
                      · rcases p5390_3 (m.d 2 4) (by simp) with h5397 | h5397
                        · linarith only [h3226, h5397, hlam]
                        · linarith only [h4905, h5397, hlam]
                      · linarith only [h3236, h5396, hlam]
                    · linarith only [h5395, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3221, h3231, h3234, hc12, hlam, hphi, p5390_1, u1ehi0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3231, h3234, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5390_1]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3231, h3234, h3237, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5390_1]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    rcases p5390_3 (m.d 0 4) (by simp) with h5406 | h5406
                    · linarith only [h3221, h5406, hlam]
                    · linarith only [h3230, h5406, hlam]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3226, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3232, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3237, hlam, p5390_1]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    rcases p5390_3 (m.d 0 4) (by simp) with h5413 | h5413
                    · rcases p5390_3 (m.d 1 4) (by simp) with h5414 | h5414
                      · rcases p5390_3 (m.d 2 4) (by simp) with h5415 | h5415
                        · rcases p5390_3 (m.d 3 4) (by simp) with h5416 | h5416
                          · rcases p5390_3 (m.d 4 5) (by simp) with h5417 | h5417
                            · linarith only [h5417, hlam, p5390_0]
                            · rcases h5bigk with h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c | h5419c
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [hlam, p5419_0]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3223, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                rcases p5419_3 (m.d 0 5) (by simp) with h5422 | h5422
                                · rcases p5419_3 (m.d 1 5) (by simp) with h5423 | h5423
                                  · rcases p5419_3 (m.d 2 5) (by simp) with h5424 | h5424
                                    · linarith only [h3227, h5424, hlam]
                                    · rcases p5419_3 (m.d 3 5) (by simp) with h5426 | h5426
                                      · linarith only [h3229, h5426, hlam]
                                      · linarith only [h4686, h5426, hlam]
                                  · linarith only [h3233, h5423, hlam]
                                · linarith only [h3227, h5422, hlam]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3230, h4686, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                rcases p5419_3 (m.d 0 5) (by simp) with h5432 | h5432
                                · rcases p5419_3 (m.d 1 5) (by simp) with h5433 | h5433
                                  · rcases p5419_3 (m.d 2 5) (by simp) with h5434 | h5434
                                    · linarith only [h3227, h5434, hlam]
                                    · linarith only [h4905, h5434, hlam]
                                  · linarith only [h3236, h5433, hlam]
                                · linarith only [h3230, h5432, hlam]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p5419_1, u1ehi0]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [hlam, p5419_0]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                rcases p5419_3 (m.d 0 5) (by simp) with h5441 | h5441
                                · linarith only [h3223, h5441, hlam]
                                · linarith only [h3227, h5441, hlam]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3231, h3234, h3236, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                rcases p5419_3 (m.d 0 5) (by simp) with h5445 | h5445
                                · linarith only [h3223, h5445, hlam]
                                · linarith only [h3230, h5445, hlam]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3227, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3233, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [hlam, p5419_0]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h4686, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4907_1, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3229, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3235, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h0, h3225, h3229, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [hlam, p5419_0]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h0, h3225, h3229, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3230, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h3236, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h4905, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [h4906, hlam, p5419_1]
                              · have p5419_0 := h5419c.1
                                have p5419_1 := h5419c.2.1
                                have p5419_2 := h5419c.2.2.1
                                have p5419_3 := h5419c.2.2.2
                                linarith only [hlam, p5419_0]
                          · linarith only [h4906, h5416, hlam]
                        · linarith only [h5415, hlam, p5390_0]
                      · linarith only [h3236, h5414, hlam]
                    · linarith only [h3230, h5413, hlam]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3228, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3234, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h0, h3225, h3228, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5390_1]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    rcases p5390_3 (m.d 0 4) (by simp) with h5471 | h5471
                    · rcases p5390_3 (m.d 1 4) (by simp) with h5472 | h5472
                      · rcases p5390_3 (m.d 2 4) (by simp) with h5473 | h5473
                        · linarith only [h3237, h5473, hlam]
                        · linarith only [h4905, h5473, hlam]
                      · linarith only [h3236, h5472, hlam]
                    · linarith only [h3230, h5471, hlam]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3230, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h3236, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h4905, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [h4906, hlam, p5390_0]
                  · have p5390_0 := h5390c.1
                    have p5390_1 := h5390c.2.1
                    have p5390_2 := h5390c.2.2.1
                    have p5390_3 := h5390c.2.2.2
                    linarith only [hlam, p5390_0]
            · linarith only [h4905, h5290, hlam]
        · linarith only [h3233, h5287, hlam]
      · linarith only [h3227, h5286, hlam]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h3227, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h3233, hlam, p4907_0]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      rcases p4907_3 (m.d 0 2) (by simp) with h5488 | h5488
      · rcases p4907_3 (m.d 1 2) (by simp) with h5489 | h5489
        · rcases p4907_3 (m.d 2 3) (by simp) with h5490 | h5490
          · linarith only [h4686, h5490, hlam]
          · rcases p4907_3 (m.d 2 4) (by simp) with h5492 | h5492
            · rcases p4907_3 (m.d 2 5) (by simp) with h5493 | h5493
              · rcases h2emax with h5494 | h5494 | h5494 | h5494 | h5494
                · linarith only [h0, h5494, hlam, ht12, u1ehi0]
                · linarith only [h5494, hlam, ht12, u1ehi1]
                · rcases h4bigk with h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c | h5497c
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3221, hlam, p5497_1]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3225, h3228, h4905, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4907_1, p5497_1]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h0, h3225, h3228, h4686, h4906, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5497_1]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    rcases p5497_3 (m.d 0 4) (by simp) with h5502 | h5502
                    · rcases p5497_3 (m.d 1 4) (by simp) with h5503 | h5503
                      · rcases p5497_3 (m.d 2 4) (by simp) with h5504 | h5504
                        · linarith only [h3226, h5504, hlam]
                        · linarith only [h4905, h5504, hlam]
                      · linarith only [h3236, h5503, hlam]
                    · linarith only [h5502, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3221, h3234, hc13, hlam, hphi, p5497_1, u1ehi0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3231, h3234, h4905, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5497_1]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3231, h3234, h4686, h4906, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5497_1]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    rcases p5497_3 (m.d 0 4) (by simp) with h5513 | h5513
                    · linarith only [h3221, h5513, hlam]
                    · linarith only [h3230, h5513, hlam]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3226, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3232, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3237, hlam, p5497_1]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    rcases p5497_3 (m.d 0 4) (by simp) with h5520 | h5520
                    · rcases p5497_3 (m.d 1 4) (by simp) with h5521 | h5521
                      · rcases p5497_3 (m.d 2 4) (by simp) with h5522 | h5522
                        · rcases p5497_3 (m.d 3 4) (by simp) with h5523 | h5523
                          · rcases p5497_3 (m.d 4 5) (by simp) with h5524 | h5524
                            · linarith only [h5524, hlam, p5497_0]
                            · rcases h5bigk with h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c | h5526c
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [hlam, p5526_0]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3223, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4907_1, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h4686, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4907_1, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                rcases p5526_3 (m.d 0 5) (by simp) with h5531 | h5531
                                · rcases p5526_3 (m.d 1 5) (by simp) with h5532 | h5532
                                  · rcases p5526_3 (m.d 2 5) (by simp) with h5533 | h5533
                                    · linarith only [h3227, h5533, hlam]
                                    · linarith only [h4905, h5533, hlam]
                                  · linarith only [h3236, h5532, hlam]
                                · linarith only [h3230, h5531, hlam]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3223, h3231, h3234, h3236, hc12, hlam, hphi, p5526_1, u1ehi0]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [hlam, p5526_0]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3231, h3234, h3236, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3231, h3234, h3236, h4686, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                rcases p5526_3 (m.d 0 5) (by simp) with h5542 | h5542
                                · linarith only [h3223, h5542, hlam]
                                · linarith only [h3230, h5542, hlam]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3227, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3233, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [hlam, p5526_0]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h4686, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h0, h3226, h4905, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3229, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3235, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h0, h3225, h3229, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [hlam, p5526_0]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h0, h3225, h3228, h4906, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3230, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h3236, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h4905, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [h4906, hlam, p5526_1]
                              · have p5526_0 := h5526c.1
                                have p5526_1 := h5526c.2.1
                                have p5526_2 := h5526c.2.2.1
                                have p5526_3 := h5526c.2.2.2
                                linarith only [hlam, p5526_0]
                          · linarith only [h4906, h5523, hlam]
                        · linarith only [h5522, hlam, p5497_0]
                      · linarith only [h3236, h5521, hlam]
                    · linarith only [h3230, h5520, hlam]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3228, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3234, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h0, h3225, h3228, h4905, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4907_1, p5497_1]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    rcases p5497_3 (m.d 0 4) (by simp) with h5568 | h5568
                    · rcases p5497_3 (m.d 1 4) (by simp) with h5569 | h5569
                      · rcases p5497_3 (m.d 2 4) (by simp) with h5570 | h5570
                        · linarith only [h3237, h5570, hlam]
                        · linarith only [h4905, h5570, hlam]
                      · linarith only [h3236, h5569, hlam]
                    · linarith only [h3230, h5568, hlam]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3230, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h3236, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h4905, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [h4906, hlam, p5497_0]
                  · have p5497_0 := h5497c.1
                    have p5497_1 := h5497c.2.1
                    have p5497_2 := h5497c.2.2.1
                    have p5497_3 := h5497c.2.2.2
                    linarith only [hlam, p5497_0]
                · linarith only [h4905, h5494, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4907_1]
                · linarith only [h5494, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4907_1]
              · linarith only [h4686, h5493, hlam]
            · linarith only [h3237, h5492, hlam]
        · linarith only [h3231, h5489, hlam]
      · linarith only [h3225, h5488, hlam]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [h4905, hlam, p4907_1]
    · have p4907_0 := h4907c.1
      have p4907_1 := h4907c.2.1
      have p4907_2 := h4907c.2.2.1
      have p4907_3 := h4907c.2.2.2
      linarith only [hlam, p4907_0]
  · linarith only [h3237, h4905, h4906, hlam]

end R2N4
