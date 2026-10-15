import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_26S4
import Jsp000404.R1LeavesN7_26S5
import Jsp000404.R1LeavesN7_26S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4844 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h5016 | h5016
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5017 | h5017
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5018 | h5018
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5019 | h5019
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5020 | h5020
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5021 | h5021
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5022 | h5022
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5023 | h5023
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5024 | h5024
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5025 | h5025
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5026 | h5026
                      · linarith only [h4844, h5016, h5020, h5025, h5026, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h3773, h5017, h5026, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3773, h5016, h5017, h5018, h5025, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h3773, h5016, h5018, h5020, h5024, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3773, h5017, h5020, h5023, hlam]
              · linarith only [h3773, h5016, h5020, h5022, hlam]
            · linarith only [h3773, h5020, h5021, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5034 | h5034
            · linarith only [h4844, h5016, h5018, h5020, h5034, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5036 | h5036
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5037 | h5037
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5038 | h5038
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5039 | h5039
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5040 | h5040
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5041 | h5041
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5042 | h5042
                          · rcases h0bigk with h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c | h5043c
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h0, hlam, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h3129, hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h3354, hlam, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h3617, hlam, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h0, h5034, h5039, hc01, hc23, hlam, hphi, ht12, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h3773, hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h4844, hlam, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h0, h5016, h5034, h5039, h5040, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5043_1, u3ehi4]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              rcases p5043_3 (m.d 0 1) (by simp) with h5054 | h5054
                              · linarith only [h3129, h5054, hlam]
                              · rcases p5043_3 (m.d 0 2) (by simp) with h5056 | h5056
                                · linarith only [h3773, h5056, hlam]
                                · linarith only [h0, h5056, hlam]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h3773, h5016, h5040, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5043_1, u3ehi4]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h3773, h4844, h5016, h5040, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5043_1, u3ehi4]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              rcases p5043_3 (m.d 0 1) (by simp) with h5062 | h5062
                              · linarith only [h3129, h5062, hlam]
                              · rcases p5043_3 (m.d 0 2) (by simp) with h5064 | h5064
                                · linarith only [h3773, h5064, hlam]
                                · linarith only [h5016, h5064, hlam]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              rcases p5043_3 (m.d 0 1) (by simp) with h5067 | h5067
                              · linarith only [h3354, h5067, hlam]
                              · rcases p5043_3 (m.d 0 2) (by simp) with h5069 | h5069
                                · linarith only [h4844, h5069, hlam]
                                · linarith only [h0, h5069, hlam]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h5016, h5040, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p5043_1, u3ehi4]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h5017, hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              rcases p5043_3 (m.d 0 1) (by simp) with h5075 | h5075
                              · linarith only [h3354, h5075, hlam]
                              · rcases p5043_3 (m.d 0 2) (by simp) with h5077 | h5077
                                · linarith only [h4844, h5077, hlam]
                                · linarith only [h5016, h5077, hlam]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h0, h5016, h5034, h5039, hc01, hc23, hlam, hphi, ht12, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h5016, hlam, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h5018, hlam, p5043_0]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [h5019, hlam, p5043_1]
                            · have p5043_0 := h5043c.1
                              have p5043_1 := h5043c.2.1
                              have p5043_2 := h5043c.2.2.1
                              have p5043_3 := h5043c.2.2.2
                              linarith only [hlam, p5043_0]
                          · linarith only [h0, h5016, h5034, h5039, h5041, h5042, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h5034, h5041, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h5034, h5039, h5040, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h5016, h5017, h5018, h5020, h5039, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h3129, h5017, h5038, hc35, hlam, hphi, u3ehi3]
                · linarith only [h3129, h5017, h5037, hlam]
              · linarith only [h0, h5016, h5036, hlam]
        · linarith only [h4844, h5016, h5019, hlam]
      · linarith only [h5017, h5018, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5094 | h5094
      · linarith only [h5017, h5094, hc34, hlam, hphi, u3ehi4]
      · linarith only [h3773, h5016, h5094, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5097 | h5097
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5098 | h5098
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5099 | h5099
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5100 | h5100
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5101 | h5101
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5102 | h5102
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5103 | h5103
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5104 | h5104
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5105 | h5105
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5106 | h5106
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5107 | h5107
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5108 | h5108
                          · rcases h0bigk with h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c | h5109c
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h0, hlam, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3129, hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3354, hlam, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3617, hlam, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h5016, h5102, hc01, hc15, hlam, hphi, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3773, hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h4844, hlam, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h5016, hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3773, h5100, hc01, hc12, hlam, hphi, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h0, h3773, h5100, hc01, hc12, hlam, hphi, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3773, h5098, h5099, h5100, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5109_1, u3ehi4]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3773, h5098, h5100, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5109_1, u3ehi4]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3773, h5097, h5100, hc01, hc12, hlam, hphi, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h0, h3773, h5097, h5100, hc01, hc12, hlam, hphi, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h5097, hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3773, h5097, h5098, h5100, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5109_1, u3ehi4]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h3773, h5098, h5100, hc01, hc12, hlam, hphi, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h0, h3773, h5098, h5100, hc01, hc12, hlam, hphi, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h5098, hlam, p5109_0]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [h5099, hlam, p5109_1]
                            · have p5109_0 := h5109c.1
                              have p5109_1 := h5109c.2.1
                              have p5109_2 := h5109c.2.2.1
                              have p5109_3 := h5109c.2.2.2
                              linarith only [hlam, p5109_0]
                          · linarith only [h3773, h5097, h5099, h5100, h5108, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h3773, h4844, h5097, h5099, h5100, h5107, hc01, hc12, hlam, hphi]
                      · linarith only [h3773, h5097, h5106, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3773, h5097, h5105, hlam]
                  · linarith only [h3773, h5098, h5100, h5104, hlam]
                · linarith only [h3773, h5097, h5100, h5103, hlam]
              · linarith only [h3773, h5097, h5100, h5102, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h3773, h5097, h5100, h5101, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5143 | h5143
            · linarith only [h0, h4844, h5100, h5143, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5145 | h5145
              · linarith only [h0, h5016, h5100, h5145, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5147 | h5147
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5148 | h5148
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5149 | h5149
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5150 | h5150
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5151 | h5151
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5152 | h5152
                          · rcases h0bigk with h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c | h5153c
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h0, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3129, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3354, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3617, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h0, h5145, h5149, h5151, hc01, hc23, hlam, hphi, ht12, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h3773, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h4844, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h5016, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5164 | h5164
                              · linarith only [h3129, h5164, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5166 | h5166
                                · linarith only [h3773, h5166, hlam]
                                · linarith only [h0, h5166, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5169 | h5169
                              · linarith only [h3129, h5169, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5171 | h5171
                                · linarith only [h3773, h5171, hlam]
                                · rcases p5153_3 (m.d 0 3) (by simp) with h5173 | h5173
                                  · rcases p5153_3 (m.d 0 4) (by simp) with h5174 | h5174
                                    · linarith only [h5097, h5174, hlam]
                                    · linarith only [h4844, h5174, hlam]
                                  · linarith only [h3773, h5173, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5179 | h5179
                              · linarith only [h3129, h5179, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5181 | h5181
                                · linarith only [h3773, h5181, hlam]
                                · rcases p5153_3 (m.d 0 3) (by simp) with h5183 | h5183
                                  · rcases p5153_3 (m.d 0 4) (by simp) with h5184 | h5184
                                    · linarith only [h5097, h5184, hlam]
                                    · rcases p5153_3 (m.d 0 5) (by simp) with h5186 | h5186
                                      · linarith only [h5098, h5186, hlam]
                                      · rcases h2bigk with h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c | h5188c
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h0, hlam, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h3773, hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h4844, hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5016, hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5145, h5149, h5151, hc02, hc23, hlam, hphi, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5100, hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5143, hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5145, hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          rcases p5188_3 (m.d 0 2) (by simp) with h5199 | h5199
                                          · linarith only [h5199, hlam, p5188_0]
                                          · rcases p5188_3 (m.d 1 2) (by simp) with h5201 | h5201
                                            · linarith only [h5100, h5201, hlam]
                                            · linarith only [h0, h5201, hlam]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h0, h4844, hc01, hc23, hlam, hphi, ht12, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h0, h5145, hc01, hc23, hlam, hphi, ht12, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          rcases p5188_3 (m.d 0 2) (by simp) with h5208 | h5208
                                          · linarith only [h5208, hlam, p5188_0]
                                          · rcases p5188_3 (m.d 1 2) (by simp) with h5210 | h5210
                                            · linarith only [h5143, h5210, hlam]
                                            · linarith only [h0, h5210, hlam]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5149, hlam, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h0, h5145, h5149, hc01, hc23, hlam, hphi, ht12, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          rcases p5188_3 (m.d 0 2) (by simp) with h5217 | h5217
                                          · linarith only [h5217, hlam, p5188_0]
                                          · rcases p5188_3 (m.d 1 2) (by simp) with h5219 | h5219
                                            · linarith only [h5145, h5219, hlam]
                                            · linarith only [h0, h5219, hlam]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5150, hlam, p5188_1]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [h5151, hlam, p5188_0]
                                        · have p5188_0 := h5188c.1
                                          have p5188_1 := h5188c.2.1
                                          have p5188_2 := h5188c.2.2.1
                                          have p5188_3 := h5188c.2.2.2
                                          linarith only [hlam, p5188_0]
                                  · linarith only [h5097, h5183, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5227 | h5227
                              · linarith only [h3129, h5227, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5229 | h5229
                                · linarith only [h3773, h5229, hlam]
                                · rcases p5153_3 (m.d 0 3) (by simp) with h5231 | h5231
                                  · rcases p5153_3 (m.d 0 4) (by simp) with h5232 | h5232
                                    · linarith only [h5097, h5232, hlam]
                                    · linarith only [h5099, h5232, hlam]
                                  · linarith only [h5098, h5231, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5236 | h5236
                              · linarith only [h3354, h5236, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5238 | h5238
                                · linarith only [h4844, h5238, hlam]
                                · linarith only [h0, h5238, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5241 | h5241
                              · linarith only [h3354, h5241, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5243 | h5243
                                · linarith only [h4844, h5243, hlam]
                                · rcases p5153_3 (m.d 0 3) (by simp) with h5245 | h5245
                                  · rcases p5153_3 (m.d 0 4) (by simp) with h5246 | h5246
                                    · rcases p5153_3 (m.d 0 5) (by simp) with h5247 | h5247
                                      · linarith only [h5099, h5247, hlam]
                                      · linarith only [h5016, h5247, hlam]
                                    · linarith only [h4844, h5246, hlam]
                                  · linarith only [h3773, h5245, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h5097, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5254 | h5254
                              · linarith only [h3354, h5254, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5256 | h5256
                                · linarith only [h4844, h5256, hlam]
                                · rcases p5153_3 (m.d 0 3) (by simp) with h5258 | h5258
                                  · rcases p5153_3 (m.d 0 4) (by simp) with h5259 | h5259
                                    · rcases p5153_3 (m.d 0 5) (by simp) with h5260 | h5260
                                      · linarith only [h5099, h5260, hlam]
                                      · rcases h2bigk with h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c | h5262c
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, hlam, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h3773, hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h4844, hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h5016, hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, h5100, hc01, hc23, hlam, hphi, ht12, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h5100, hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h5143, hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h5145, hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          rcases p5262_3 (m.d 0 2) (by simp) with h5273 | h5273
                                          · linarith only [h5273, hlam, p5262_0]
                                          · rcases p5262_3 (m.d 1 2) (by simp) with h5275 | h5275
                                            · linarith only [h5100, h5275, hlam]
                                            · linarith only [h0, h5275, hlam]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, h4844, hc01, hc23, hlam, hphi, ht12, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, h5016, hc01, hc23, hlam, hphi, ht12, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          rcases p5262_3 (m.d 0 2) (by simp) with h5282 | h5282
                                          · linarith only [h5282, hlam, p5262_0]
                                          · rcases p5262_3 (m.d 1 2) (by simp) with h5284 | h5284
                                            · linarith only [h5143, h5284, hlam]
                                            · linarith only [h0, h5284, hlam]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h5149, hlam, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, h5145, h5149, hc01, hc23, hlam, hphi, ht12, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          rcases p5262_3 (m.d 0 2) (by simp) with h5291 | h5291
                                          · linarith only [h5291, hlam, p5262_0]
                                          · rcases p5262_3 (m.d 1 2) (by simp) with h5293 | h5293
                                            · linarith only [h5145, h5293, hlam]
                                            · linarith only [h0, h5293, hlam]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h5150, hlam, p5262_1]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [h5151, hlam, p5262_0]
                                        · have p5262_0 := h5262c.1
                                          have p5262_1 := h5262c.2.1
                                          have p5262_2 := h5262c.2.2.1
                                          have p5262_3 := h5262c.2.2.2
                                          linarith only [hlam, p5262_0]
                                    · linarith only [h5099, h5259, hlam]
                                  · linarith only [h5098, h5258, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5302 | h5302
                              · linarith only [h3617, h5302, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5304 | h5304
                                · linarith only [h5016, h5304, hlam]
                                · linarith only [h0, h5304, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              rcases p5153_3 (m.d 0 1) (by simp) with h5307 | h5307
                              · linarith only [h3617, h5307, hlam]
                              · rcases p5153_3 (m.d 0 2) (by simp) with h5309 | h5309
                                · linarith only [h5016, h5309, hlam]
                                · rcases p5153_3 (m.d 0 3) (by simp) with h5311 | h5311
                                  · rcases p5153_3 (m.d 0 4) (by simp) with h5312 | h5312
                                    · rcases p5153_3 (m.d 0 5) (by simp) with h5313 | h5313
                                      · rcases h2bigk with h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c | h5314c
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h0, hlam, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h3773, hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h4844, hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h5016, hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h0, h5100, hc01, hc23, hlam, hphi, ht12, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h5100, hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h5143, hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h5145, hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          rcases p5314_3 (m.d 0 2) (by simp) with h5325 | h5325
                                          · linarith only [h5325, hlam, p5314_0]
                                          · rcases p5314_3 (m.d 1 2) (by simp) with h5327 | h5327
                                            · linarith only [h5100, h5327, hlam]
                                            · linarith only [h0, h5327, hlam]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h3354, h5143, hc01, hc23, hlam, hphi, ht12, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h0, h3617, h5145, hc01, hc23, hlam, hphi, ht12, p5153_1, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          rcases p5314_3 (m.d 0 2) (by simp) with h5334 | h5334
                                          · linarith only [h5334, hlam, p5314_0]
                                          · rcases p5314_3 (m.d 1 2) (by simp) with h5336 | h5336
                                            · linarith only [h5143, h5336, hlam]
                                            · linarith only [h0, h5336, hlam]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h5149, hlam, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h0, h3617, h5145, h5149, hc01, hc23, hlam, hphi, ht12, p5153_1, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          rcases p5314_3 (m.d 0 2) (by simp) with h5343 | h5343
                                          · linarith only [h5343, hlam, p5314_0]
                                          · rcases p5314_3 (m.d 1 2) (by simp) with h5345 | h5345
                                            · linarith only [h5145, h5345, hlam]
                                            · linarith only [h0, h5345, hlam]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h5150, hlam, p5314_1]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [h5151, hlam, p5314_0]
                                        · have p5314_0 := h5314c.1
                                          have p5314_1 := h5314c.2.1
                                          have p5314_2 := h5314c.2.2.1
                                          have p5314_3 := h5314c.2.2.2
                                          linarith only [hlam, p5314_0]
                                      · linarith only [h5016, h5313, hlam]
                                    · linarith only [h4844, h5312, hlam]
                                  · linarith only [h3773, h5311, hlam]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h5098, hlam, p5153_0]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [h5099, hlam, p5153_1]
                            · have p5153_0 := h5153c.1
                              have p5153_1 := h5153c.2.1
                              have p5153_2 := h5153c.2.2.1
                              have p5153_3 := h5153c.2.2.2
                              linarith only [hlam, p5153_0]
                          · rcases h0bigk with h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h0, hlam, p5358_1]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h3129, hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h3354, hlam, p5358_1]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h3617, hlam, p5358_1]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h3773, hc01, hc23, hlam, hphi, ht12, p5358_1]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h3773, hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h4844, hlam, p5358_1]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h5016, hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              rcases p5358_3 (m.d 0 1) (by simp) with h5369 | h5369
                              · linarith only [h3129, h5369, hlam]
                              · rcases p5358_3 (m.d 0 2) (by simp) with h5371 | h5371
                                · linarith only [h3773, h5371, hlam]
                                · linarith only [h0, h5371, hlam]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              rcases p5358_3 (m.d 0 1) (by simp) with h5374 | h5374
                              · linarith only [h3129, h5374, hlam]
                              · rcases p5358_3 (m.d 0 2) (by simp) with h5376 | h5376
                                · linarith only [h3773, h5376, hlam]
                                · rcases p5358_3 (m.d 0 3) (by simp) with h5378 | h5378
                                  · rcases p5358_3 (m.d 0 4) (by simp) with h5379 | h5379
                                    · linarith only [h5097, h5379, hlam]
                                    · linarith only [h4844, h5379, hlam]
                                  · linarith only [h3773, h5378, hlam]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h3129, h5099, h5100, h5152, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5358_1]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h3129, h5099, h5100, h5152, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5358_1, u3ehi3]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              rcases p5358_3 (m.d 0 1) (by simp) with h5386 | h5386
                              · linarith only [h3354, h5386, hlam]
                              · rcases p5358_3 (m.d 0 2) (by simp) with h5388 | h5388
                                · linarith only [h4844, h5388, hlam]
                                · linarith only [h0, h5388, hlam]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              rcases p5358_3 (m.d 0 1) (by simp) with h5391 | h5391
                              · linarith only [h3354, h5391, hlam]
                              · rcases p5358_3 (m.d 0 2) (by simp) with h5393 | h5393
                                · linarith only [h4844, h5393, hlam]
                                · rcases p5358_3 (m.d 0 3) (by simp) with h5395 | h5395
                                  · rcases p5358_3 (m.d 0 4) (by simp) with h5396 | h5396
                                    · rcases p5358_3 (m.d 0 5) (by simp) with h5397 | h5397
                                      · linarith only [h5099, h5397, hlam]
                                      · linarith only [h5016, h5397, hlam]
                                    · linarith only [h4844, h5396, hlam]
                                  · linarith only [h3773, h5395, hlam]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h5097, hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h5099, h5152, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p5358_1, u3ehi3]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              rcases p5358_3 (m.d 0 1) (by simp) with h5405 | h5405
                              · linarith only [h3617, h5405, hlam]
                              · rcases p5358_3 (m.d 0 2) (by simp) with h5407 | h5407
                                · linarith only [h5016, h5407, hlam]
                                · linarith only [h0, h5407, hlam]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              rcases p5358_3 (m.d 0 1) (by simp) with h5410 | h5410
                              · linarith only [h3617, h5410, hlam]
                              · rcases p5358_3 (m.d 0 2) (by simp) with h5412 | h5412
                                · linarith only [h5016, h5412, hlam]
                                · rcases p5358_3 (m.d 0 3) (by simp) with h5414 | h5414
                                  · rcases p5358_3 (m.d 0 4) (by simp) with h5415 | h5415
                                    · rcases p5358_3 (m.d 0 5) (by simp) with h5416 | h5416
                                      · rcases h2bigk with h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c | h5417c
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h0, hlam, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h3773, hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h4844, hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h5016, hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h0, h5145, h5149, h5151, hc01, hc23, hlam, hphi, ht12, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h5100, hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h5143, hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h5145, hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          rcases p5417_3 (m.d 0 2) (by simp) with h5428 | h5428
                                          · linarith only [h5428, hlam, p5417_0]
                                          · rcases p5417_3 (m.d 1 2) (by simp) with h5430 | h5430
                                            · linarith only [h5100, h5430, hlam]
                                            · linarith only [h0, h5430, hlam]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h3354, h5143, hc01, hc23, hlam, hphi, ht12, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h0, h3617, h5145, hc01, hc23, hlam, hphi, ht12, p5358_1, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          rcases p5417_3 (m.d 0 2) (by simp) with h5437 | h5437
                                          · linarith only [h5437, hlam, p5417_0]
                                          · rcases p5417_3 (m.d 1 2) (by simp) with h5439 | h5439
                                            · linarith only [h5143, h5439, hlam]
                                            · linarith only [h0, h5439, hlam]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h5149, hlam, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h0, h3617, h5145, h5149, hc01, hc23, hlam, hphi, ht12, p5358_1, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          rcases p5417_3 (m.d 0 2) (by simp) with h5446 | h5446
                                          · linarith only [h5446, hlam, p5417_0]
                                          · rcases p5417_3 (m.d 1 2) (by simp) with h5448 | h5448
                                            · linarith only [h5145, h5448, hlam]
                                            · linarith only [h0, h5448, hlam]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h5150, hlam, p5417_1]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [h5151, hlam, p5417_0]
                                        · have p5417_0 := h5417c.1
                                          have p5417_1 := h5417c.2.1
                                          have p5417_2 := h5417c.2.2.1
                                          have p5417_3 := h5417c.2.2.2
                                          linarith only [hlam, p5417_0]
                                      · linarith only [h5016, h5416, hlam]
                                    · linarith only [h4844, h5415, hlam]
                                  · linarith only [h3773, h5414, hlam]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h5098, hlam, p5358_0]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [h5099, hlam, p5358_1]
                            · have p5358_0 := h5358c.1
                              have p5358_1 := h5358c.2.1
                              have p5358_2 := h5358c.2.2.1
                              have p5358_3 := h5358c.2.2.2
                              linarith only [hlam, p5358_0]
                        · linarith only [h0, h3354, h4844, h5099, h5151, hc01, hc14, hlam, hphi]
                      · linarith only [h3129, h5097, h5100, h5150, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h3129, h5097, h5100, h5149, hlam]
                  · linarith only [h3129, h5098, h5148, hlam]
                · linarith only [h3129, h5097, h5147, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5466 | h5466
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5467 | h5467
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5468 | h5468
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5469 | h5469
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5470 | h5470
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5471 | h5471
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5472 | h5472
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5473 | h5473
                        · linarith only [h3354, h5099, h5467, h5473, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5475 | h5475
                          · linarith only [h0, h4844, h5097, h5473, h5475, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases h0bigk with h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h0, hlam, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3129, hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3354, hlam, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3617, hlam, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h4844, hc01, hc24, hlam, hphi, ht12, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3773, hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h4844, hlam, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h5016, hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3773, h5466, hc01, hc12, hlam, hphi, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h0, h3773, h5466, hc01, hc12, hlam, hphi, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3354, h3773, h5466, hc01, hc12, hlam, hphi, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3617, h3773, h5466, hc01, hc12, hlam, hphi, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3773, h4844, h5098, h5466, h5473, h5475, hc01, hc12, hc45, hlam, hphi, ht34, p5477_1, u3ehi3]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h0, h3773, h4844, h5098, h5466, h5473, h5475, hc01, hc12, hc45, hlam, hphi, ht34, p5477_1, u3ehi3]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h5097, hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h5099, hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h5016, h5466, h5472, hc01, hc12, hlam, hphi, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h0, h5016, h5466, h5472, hc01, hc12, hlam, hphi, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h5098, hlam, p5477_0]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [h3354, h5016, h5466, h5472, hc01, hc12, hlam, hphi, p5477_1]
                            · have p5477_0 := h5477c.1
                              have p5477_1 := h5477c.2.1
                              have p5477_2 := h5477c.2.2.1
                              have p5477_3 := h5477c.2.2.2
                              linarith only [hlam, p5477_0]
                      · linarith only [h3773, h5098, h5472, hlam]
                    · linarith only [h3773, h5098, h5471, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h3773, h5098, h5466, h5470, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h3773, h5097, h5466, h5469, hlam]
              · linarith only [h3773, h5097, h5466, h5468, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h3773, h5097, h5466, h5467, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5509 | h5509
            · linarith only [h0, h4844, h5466, h5509, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5511 | h5511
              · linarith only [h0, h5016, h5509, h5511, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5513 | h5513
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5514 | h5514
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5515 | h5515
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5516 | h5516
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5517 | h5517
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5518 | h5518
                          · linarith only [h3129, h3354, h5097, h5099, h5518, hc01, hc13, hlam, hphi]
                          · rcases h0bigk with h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, hlam, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h3129, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h3354, hlam, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h3617, hlam, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, h5511, h5515, h5517, hc01, hc23, hlam, hphi, ht12, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h3773, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h4844, hlam, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5016, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              rcases p5520_3 (m.d 0 1) (by simp) with h5531 | h5531
                              · linarith only [h3129, h5531, hlam]
                              · rcases p5520_3 (m.d 0 2) (by simp) with h5533 | h5533
                                · linarith only [h3773, h5533, hlam]
                                · linarith only [h0, h5533, hlam]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              rcases p5520_3 (m.d 0 1) (by simp) with h5536 | h5536
                              · linarith only [h3129, h5536, hlam]
                              · rcases p5520_3 (m.d 0 2) (by simp) with h5538 | h5538
                                · linarith only [h3773, h5538, hlam]
                                · rcases p5520_3 (m.d 0 3) (by simp) with h5540 | h5540
                                  · rcases p5520_3 (m.d 0 4) (by simp) with h5541 | h5541
                                    · linarith only [h5097, h5541, hlam]
                                    · linarith only [h4844, h5541, hlam]
                                  · linarith only [h3773, h5540, hlam]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              rcases p5520_3 (m.d 0 1) (by simp) with h5546 | h5546
                              · linarith only [h3129, h5546, hlam]
                              · rcases p5520_3 (m.d 0 2) (by simp) with h5548 | h5548
                                · linarith only [h3773, h5548, hlam]
                                · rcases p5520_3 (m.d 0 3) (by simp) with h5550 | h5550
                                  · rcases p5520_3 (m.d 0 4) (by simp) with h5551 | h5551
                                    · linarith only [h5097, h5551, hlam]
                                    · rcases p5520_3 (m.d 0 5) (by simp) with h5553 | h5553
                                      · linarith only [h5098, h5553, hlam]
                                      · linarith only [h5099, h5553, hlam]
                                  · linarith only [h5097, h5550, hlam]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              rcases p5520_3 (m.d 0 1) (by simp) with h5557 | h5557
                              · linarith only [h3129, h5557, hlam]
                              · rcases p5520_3 (m.d 0 2) (by simp) with h5559 | h5559
                                · linarith only [h3773, h5559, hlam]
                                · rcases p5520_3 (m.d 0 3) (by simp) with h5561 | h5561
                                  · rcases p5520_3 (m.d 0 4) (by simp) with h5562 | h5562
                                    · linarith only [h5097, h5562, hlam]
                                    · rcases p5520_3 (m.d 0 5) (by simp) with h5564 | h5564
                                      · linarith only [h5098, h5564, hlam]
                                      · rcases h2bigk with h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h0, hlam, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h3773, hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h4844, hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h5016, hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h0, h5511, h5517, hc01, hc24, hlam, hphi, ht12, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h5466, hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h5509, hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h5511, hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          rcases p5566_3 (m.d 0 2) (by simp) with h5577 | h5577
                                          · linarith only [h5577, hlam, p5566_0]
                                          · rcases p5566_3 (m.d 1 2) (by simp) with h5579 | h5579
                                            · linarith only [h5466, h5579, hlam]
                                            · linarith only [h0, h5579, hlam]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h3617, h5511, h5517, hc01, hc23, hlam, hphi, ht12, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h0, h5511, hc01, hc23, hlam, hphi, ht12, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          rcases p5566_3 (m.d 0 2) (by simp) with h5586 | h5586
                                          · linarith only [h5586, hlam, p5566_0]
                                          · rcases p5566_3 (m.d 1 2) (by simp) with h5588 | h5588
                                            · linarith only [h5509, h5588, hlam]
                                            · linarith only [h0, h5588, hlam]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h0, hc01, hc24, hlam, hphi, ht12, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h5515, hlam, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h0, h5511, h5515, hc01, hc23, hlam, hphi, ht12, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          rcases p5566_3 (m.d 0 2) (by simp) with h5595 | h5595
                                          · linarith only [h5595, hlam, p5566_0]
                                          · rcases p5566_3 (m.d 1 2) (by simp) with h5597 | h5597
                                            · linarith only [h5511, h5597, hlam]
                                            · linarith only [h0, h5597, hlam]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h0, hc01, hc25, hlam, hphi, ht12, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h5516, hlam, p5566_1]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [h5517, hlam, p5566_0]
                                        · have p5566_0 := h5566c.1
                                          have p5566_1 := h5566c.2.1
                                          have p5566_2 := h5566c.2.2.1
                                          have p5566_3 := h5566c.2.2.2
                                          linarith only [hlam, p5566_0]
                                  · linarith only [h5098, h5561, hlam]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5099, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, h5099, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5097, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5099, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5099, h5515, h5517, hc01, hc23, hlam, hphi, ht12, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, h5099, h5515, h5517, hc01, hc23, hlam, hphi, ht12, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5098, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5097, h5099, h5515, h5517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5520_1, u3ehi3]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                        · linarith only [h0, h5509, h5517, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h3129, h5098, h5466, h5516, hlam]
                    · linarith only [h3129, h5098, h5466, h5515, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h3129, h5098, h5514, hlam]
                · linarith only [h3129, h5097, h5513, hlam]
      · linarith only [h5097, h5098, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5621 | h5621
      · linarith only [h5097, h5621, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5623 | h5623
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5624 | h5624
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5625 | h5625
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5626 | h5626
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5627 | h5627
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5628 | h5628
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5629 | h5629
                    · linarith only [h5097, h5624, h5629, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h3773, h5624, h5627, h5629, hc01, hc12, hlam, hphi]
                  · linarith only [h5627, h5628, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5633 | h5633
                  · linarith only [h5627, h5633, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5635 | h5635
                    · linarith only [h3129, h5627, h5635, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5637 | h5637
                      · linarith only [h5624, h5633, h5637, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5639 | h5639
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5640 | h5640
                          · rcases h0bigk with h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h3129, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h3354, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h3617, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h3773, h5624, hc01, hc13, hlam, hphi, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h3773, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h4844, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5016, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h3129, h5633, h5640, hc01, hc34, hlam, hphi, ht12, ht23, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h3773, h5624, h5633, h5640, hc02, hc34, hlam, hphi, ht23, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5097, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5621, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h4844, h5625, hc01, hc12, hlam, hphi, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, h4844, h5625, hc01, hc12, hlam, hphi, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h4844, h5625, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5641_1, u3ehi0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h4844, h5621, h5625, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5641_1, u3ehi0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5016, h5625, h5639, hc01, hc12, hlam, hphi, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, h5016, h5625, h5639, hc01, hc12, hlam, hphi, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5016, h5625, h5639, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5641_1, u3ehi0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5623, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                          · linarith only [h4844, h5623, h5625, h5640, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h3354, h4844, h5623, h5639, hc01, hc14, hlam, hphi]
              · linarith only [h0, h4844, h5625, h5626, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h3773, h5624, h5625, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5671 | h5671
            · linarith only [h0, h4844, h5624, h5671, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5673 | h5673
              · linarith only [h0, h5016, h5624, h5673, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5675 | h5675
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5676 | h5676
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5677 | h5677
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5678 | h5678
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5679 | h5679
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5680 | h5680
                          · rcases h0bigk with h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c | h5681c
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [hlam, p5681_0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h0, hlam, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h3129, hlam, p5681_0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h3354, hlam, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h3617, hlam, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h0, h5673, h5677, h5679, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [hlam, p5681_0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h3773, hlam, p5681_0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h4844, hlam, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5016, hlam, p5681_0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5097, h5624, h5675, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h0, h5097, h5624, h5675, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [hlam, p5681_0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5097, hlam, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5621, hlam, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5097, h5624, h5675, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h0, h5097, h5624, h5675, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5097, h5624, h5675, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5681_1, u3ehi0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [hlam, p5681_0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h3617, h5097, h5624, h5675, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5621, h5624, h5675, h5680, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h0, h5621, h5624, h5675, h5680, hc01, hc23, hlam, hphi, ht12, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5621, h5624, h5675, h5680, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5681_1, u3ehi0]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [h5623, hlam, p5681_1]
                            · have p5681_0 := h5681c.1
                              have p5681_1 := h5681c.2.1
                              have p5681_2 := h5681c.2.2.1
                              have p5681_3 := h5681c.2.2.2
                              linarith only [hlam, p5681_0]
                          · linarith only [h5097, h5623, h5680, hlam]
                        · linarith only [h0, h4844, h5097, h5623, h5624, h5675, h5679, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h5624, h5675, h5678, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h5624, h5675, h5677, hlam]
                  · linarith only [h5675, h5676, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5712 | h5712
                  · linarith only [h5675, h5712, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5714 | h5714
                    · linarith only [h3129, h5675, h5714, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5624, h5714, hc01, hc34, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5717 | h5717
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5718 | h5718
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5719 | h5719
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5720 | h5720
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5721 | h5721
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5722 | h5722
                    · linarith only [h5097, h5717, h5722, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h0, h3773, h5720, h5722, hc01, hc13, hlam, hphi]
                  · linarith only [h5097, h5720, h5721, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5726 | h5726
                  · linarith only [h5720, h5726, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5728 | h5728
                    · linarith only [h3129, h5720, h5728, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5730 | h5730
                      · linarith only [h5717, h5720, h5730, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5732 | h5732
                        · linarith only [h5097, h5623, h5718, h5732, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5734 | h5734
                          · linarith only [h0, h3773, h5728, h5732, h5734, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h5720, h5734, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h0, h3773, h5717, h5719, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h3773, h5717, h5718, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5739 | h5739
            · linarith only [h0, h4844, h5717, h5739, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5741 | h5741
              · linarith only [h0, h5016, h5717, h5741, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5743 | h5743
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5744 | h5744
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5745 | h5745
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5746 | h5746
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5747 | h5747
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5748 | h5748
                          · linarith only [h5097, h5623, h5748, hc34, hlam, hphi, u3ehi0]
                          · linarith only [h5097, h5745, h5747, h5748, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h5739, h5747, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h5097, h5717, h5743, h5744, h5746, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h5717, h5743, h5745, hlam]
                  · linarith only [h5097, h5743, h5744, hc35, hlam, hphi, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5755 | h5755
                  · linarith only [h5621, h5743, h5755, hc34, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5757 | h5757
                    · linarith only [h3129, h5743, h5757, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h5717, h5757, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3773 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4844 | h4844
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x1_x0 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h4844
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x1_x1 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773 h4844

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3617 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3773 | h3773
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x0 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1_x1 m hb0 hb2 hb3 hg0 h3129 h3354 h3617 h3773

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3354 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3617 | h3617
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x0 m hb0 hb2 hb3 hg0 h3129 h3354 h3617
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1_x1 m hb0 hb2 hb3 hg0 h3129 h3354 h3617

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3129 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3354 | h3354
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x0 m hb0 hb2 hb3 hg0 h3129 h3354
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1_x1 m hb0 hb2 hb3 hg0 h3129 h3354

set_option maxHeartbeats 5262000 in
set_option maxHeartbeats 5262000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h3129 | h3129
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x0 m hb0 hb2 hb3 hg0 h3129
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3_x1 m hb0 hb2 hb3 hg0 h3129

set_option maxHeartbeats 11520000 in
set_option maxHeartbeats 11520000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_I_L_I_M_IR_s3 m hb0 hb2 hb3 h0

end R2N4
