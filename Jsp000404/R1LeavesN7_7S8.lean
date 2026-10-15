import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10712000 in
set_option maxHeartbeats 10712000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s6 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5099 | h5099
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5100 | h5100
      · linarith only [h4, h5100, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5102 | h5102
        · linarith only [h4, h5099, h5102, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5104 | h5104
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5105 | h5105
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5106 | h5106
              · linarith only [h0, h5106, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5108 | h5108
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5109 | h5109
                  · linarith only [h1, h5100, h5109, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5111 | h5111
                    · linarith only [h2, h5102, h5111, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5113 | h5113
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5114 | h5114
                        · linarith only [h0, h1, h5100, h5104, h5114, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5116 | h5116
                          · linarith only [h1, h4, h5102, h5105, h5108, h5113, h5116, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h5104, h5113, h5116, h6, hc34, hc45, hlam, hphi]
                      · linarith only [h5099, h5100, h5113, hc23, hc35, hlam, hphi]
                · linarith only [h5099, h5100, h5108, hc13, hc35, hlam, hphi]
            · linarith only [h5, h5105, h6, hc12, hc25, hlam, hphi]
          · linarith only [h4, h5104, h6, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5123 | h5123
      · linarith only [h5, h5099, h5123, h6, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5125 | h5125
        · linarith only [h5, h5125, h6, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5127 | h5127
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5128 | h5128
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5129 | h5129
              · linarith only [h0, h5129, h6, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5131 | h5131
                · linarith only [h1, h5099, h5131, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5133 | h5133
                  · linarith only [h1, h4, h5099, h5123, h5133, h6, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5135 | h5135
                    · linarith only [h2, h5125, h5135, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5137 | h5137
                      · linarith only [h0, h1, h5099, h5127, h5137, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5139 | h5139
                        · linarith only [h4, h5123, h5139, h6, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5141 | h5141
                          · linarith only [h5, h5125, h5141, h6, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5143 | h5143
                            · linarith only [h0, h5128, h5137, h5141, h5143, h6, hc23, hc34, hlam, hphi]
                            · rcases h1bigk with h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c | h5145c
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                rcases p5145_3 (m.d 0 1) (by simp) with h5147 | h5147
                                · rcases p5145_3 (m.d 1 2) (by simp) with h5148 | h5148
                                  · linarith only [h5148, hlam, p5145_0]
                                  · rcases p5145_3 (m.d 1 3) (by simp) with h5150 | h5150
                                    · linarith only [h1, h5150, hlam]
                                    · rcases p5145_3 (m.d 1 4) (by simp) with h5152 | h5152
                                      · linarith only [h2, h5152, hlam]
                                      · rcases p5145_3 (m.d 1 5) (by simp) with h5154 | h5154
                                        · linarith only [h3, h5154, hlam]
                                        · linarith only [h5129, h5154, hlam]
                                · linarith only [h5147, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                rcases p5145_3 (m.d 0 1) (by simp) with h5158 | h5158
                                · rcases p5145_3 (m.d 1 2) (by simp) with h5159 | h5159
                                  · linarith only [h0, h5159, hlam]
                                  · linarith only [h5127, h5159, hlam]
                                · linarith only [h5158, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                rcases p5145_3 (m.d 0 1) (by simp) with h5163 | h5163
                                · rcases p5145_3 (m.d 1 2) (by simp) with h5164 | h5164
                                  · linarith only [h0, h5164, hlam]
                                  · linarith only [h5128, h5164, hlam]
                                · linarith only [h5163, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                rcases p5145_3 (m.d 0 1) (by simp) with h5168 | h5168
                                · rcases p5145_3 (m.d 1 2) (by simp) with h5169 | h5169
                                  · linarith only [h0, h5169, hlam]
                                  · rcases p5145_3 (m.d 1 3) (by simp) with h5171 | h5171
                                    · linarith only [h1, h5171, hlam]
                                    · rcases p5145_3 (m.d 1 4) (by simp) with h5173 | h5173
                                      · linarith only [h2, h5173, hlam]
                                      · rcases p5145_3 (m.d 1 5) (by simp) with h5175 | h5175
                                        · linarith only [h5175, hlam, p5145_0]
                                        · rcases h1emax with h5177 | h5177 | h5177 | h5177 | h5177
                                          · linarith only [h0, h5128, h5137, h5177, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                          · rcases h3bigk with h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c | h5179c
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5099, h5143, hc13, hc45, hlam, hphi, ht34, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5099, h5143, hc23, hc45, hlam, hphi, ht34, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5099, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5123, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h1, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h1, h5099, h5143, hc23, hc45, hlam, hphi, ht34, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5131, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5133, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h4, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5127, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5137, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5139, hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5143, hc03, hc45, hlam, hphi, ht34, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5143, hc13, hc45, hlam, hphi, ht34, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5143, hc23, hc45, hlam, hphi, ht34, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [hlam, p5179_0]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5143, hlam, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              rcases p5179_3 (m.d 0 3) (by simp) with h5200 | h5200
                                              · linarith only [h5200, hlam, p5179_0]
                                              · rcases p5179_3 (m.d 1 3) (by simp) with h5202 | h5202
                                                · linarith only [h5133, h5202, hlam]
                                                · rcases p5179_3 (m.d 2 3) (by simp) with h5204 | h5204
                                                  · linarith only [h5139, h5204, hlam]
                                                  · rcases p5179_3 (m.d 3 4) (by simp) with h5206 | h5206
                                                    · linarith only [h5143, h5206, hlam]
                                                    · linarith only [h5099, h5206, hlam]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              rcases p5179_3 (m.d 0 3) (by simp) with h5209 | h5209
                                              · linarith only [h5123, h5209, hlam]
                                              · linarith only [h1, h5209, hlam]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              rcases p5179_3 (m.d 0 3) (by simp) with h5212 | h5212
                                              · linarith only [h5123, h5212, hlam]
                                              · linarith only [h4, h5212, hlam]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [h5099, h5143, hc03, hc45, hlam, hphi, ht34, p5179_1]
                                            · have p5179_0 := h5179c.1
                                              have p5179_1 := h5179c.2.1
                                              have p5179_2 := h5179c.2.2.1
                                              have p5179_3 := h5179c.2.2.2
                                              linarith only [hlam, p5179_0]
                                          · rcases h3bigk with h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c | h5217c
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5099, h5127, hc23, hc34, hlam, hphi, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5099, hc23, hc34, hlam, hphi, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5099, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5123, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h1, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h1, h5099, hc23, hc34, hlam, hphi, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5131, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5133, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h4, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5127, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5137, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5139, hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5143, hc03, hc45, hlam, hphi, ht34, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5127, h5143, hc23, hc45, hlam, hphi, ht34, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5143, hc23, hc45, hlam, hphi, ht34, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [hlam, p5217_0]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h5143, hlam, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              rcases p5217_3 (m.d 0 3) (by simp) with h5238 | h5238
                                              · linarith only [h5238, hlam, p5217_0]
                                              · rcases p5217_3 (m.d 1 3) (by simp) with h5240 | h5240
                                                · linarith only [h5133, h5240, hlam]
                                                · rcases p5217_3 (m.d 2 3) (by simp) with h5242 | h5242
                                                  · linarith only [h5139, h5242, hlam]
                                                  · rcases p5217_3 (m.d 3 4) (by simp) with h5244 | h5244
                                                    · linarith only [h5143, h5244, hlam]
                                                    · linarith only [h5099, h5244, hlam]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              rcases p5217_3 (m.d 0 3) (by simp) with h5247 | h5247
                                              · linarith only [h5123, h5247, hlam]
                                              · linarith only [h1, h5247, hlam]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              rcases p5217_3 (m.d 0 3) (by simp) with h5250 | h5250
                                              · linarith only [h5123, h5250, hlam]
                                              · linarith only [h4, h5250, hlam]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [h1, h5099, h5127, h5143, hc23, hc45, hlam, hphi, ht34, p5217_1]
                                            · have p5217_0 := h5217c.1
                                              have p5217_1 := h5217c.2.1
                                              have p5217_2 := h5217c.2.2.1
                                              have p5217_3 := h5217c.2.2.2
                                              linarith only [hlam, p5217_0]
                                          · rcases h3bigk with h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c | h5255c
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5099, h5127, hc23, hc34, hlam, hphi, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5099, hc23, hc34, hlam, hphi, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5099, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5123, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h1, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h1, h5099, hc23, hc34, hlam, hphi, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5131, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5133, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h4, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5127, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5137, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5139, hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5143, hc03, hc45, hlam, hphi, ht34, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5127, h5143, hc23, hc45, hlam, hphi, ht34, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5143, hc23, hc45, hlam, hphi, ht34, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [hlam, p5255_0]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h5143, hlam, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              rcases p5255_3 (m.d 0 3) (by simp) with h5276 | h5276
                                              · linarith only [h5276, hlam, p5255_0]
                                              · rcases p5255_3 (m.d 1 3) (by simp) with h5278 | h5278
                                                · linarith only [h5133, h5278, hlam]
                                                · rcases p5255_3 (m.d 2 3) (by simp) with h5280 | h5280
                                                  · linarith only [h5139, h5280, hlam]
                                                  · rcases p5255_3 (m.d 3 4) (by simp) with h5282 | h5282
                                                    · linarith only [h5143, h5282, hlam]
                                                    · linarith only [h5099, h5282, hlam]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              rcases p5255_3 (m.d 0 3) (by simp) with h5285 | h5285
                                              · linarith only [h5123, h5285, hlam]
                                              · linarith only [h1, h5285, hlam]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              rcases p5255_3 (m.d 0 3) (by simp) with h5288 | h5288
                                              · linarith only [h5123, h5288, hlam]
                                              · linarith only [h4, h5288, hlam]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [h1, h5099, h5127, h5143, hc23, hc45, hlam, hphi, ht34, p5255_1]
                                            · have p5255_0 := h5255c.1
                                              have p5255_1 := h5255c.2.1
                                              have p5255_2 := h5255c.2.2.1
                                              have p5255_3 := h5255c.2.2.2
                                              linarith only [hlam, p5255_0]
                                          · rcases h3bigk with h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c | h5293c
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5099, h5127, hc23, hc34, hlam, hphi, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5099, hc23, hc34, hlam, hphi, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5099, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5123, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h1, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h1, h5099, hc23, hc34, hlam, hphi, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5131, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5133, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h4, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5127, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5137, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5139, hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5143, hc03, hc45, hlam, hphi, ht34, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5127, h5143, hc23, hc45, hlam, hphi, ht34, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5143, hc23, hc45, hlam, hphi, ht34, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [hlam, p5293_0]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h5143, hlam, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              rcases p5293_3 (m.d 0 3) (by simp) with h5314 | h5314
                                              · linarith only [h5314, hlam, p5293_0]
                                              · rcases p5293_3 (m.d 1 3) (by simp) with h5316 | h5316
                                                · linarith only [h5133, h5316, hlam]
                                                · rcases p5293_3 (m.d 2 3) (by simp) with h5318 | h5318
                                                  · linarith only [h5139, h5318, hlam]
                                                  · rcases p5293_3 (m.d 3 4) (by simp) with h5320 | h5320
                                                    · linarith only [h5143, h5320, hlam]
                                                    · linarith only [h5099, h5320, hlam]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              rcases p5293_3 (m.d 0 3) (by simp) with h5323 | h5323
                                              · linarith only [h5123, h5323, hlam]
                                              · linarith only [h1, h5323, hlam]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              rcases p5293_3 (m.d 0 3) (by simp) with h5326 | h5326
                                              · linarith only [h5123, h5326, hlam]
                                              · linarith only [h4, h5326, hlam]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [h1, h5099, h5127, h5143, hc23, hc45, hlam, hphi, ht34, p5293_1]
                                            · have p5293_0 := h5293c.1
                                              have p5293_1 := h5293c.2.1
                                              have p5293_2 := h5293c.2.2.1
                                              have p5293_3 := h5293c.2.2.2
                                              linarith only [hlam, p5293_0]
                                · linarith only [h5168, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h0, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h0, h5127, h5139, h5143, h6, hc23, hc45, hlam, hphi, ht34, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h0, h5128, h5137, h5139, h5143, h6, hc23, hc45, hlam, hphi, ht34, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h5129, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h1, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h5127, hlam, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h5131, hlam, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h5133, hlam, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h2, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h5128, hlam, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h2, h5125, h5127, hc23, hc45, hlam, hphi, ht34, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h5135, hlam, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h3, hlam, p5145_0]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [h3, h5123, h5127, h5143, hc23, hc45, hlam, hphi, ht34, p5145_1]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                rcases p5145_3 (m.d 0 1) (by simp) with h5349 | h5349
                                · rcases p5145_3 (m.d 1 2) (by simp) with h5350 | h5350
                                  · linarith only [h5129, h5350, hlam]
                                  · linarith only [h5127, h5350, hlam]
                                · linarith only [h1, h5349, hlam]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                rcases p5145_3 (m.d 0 1) (by simp) with h5354 | h5354
                                · rcases p5145_3 (m.d 1 2) (by simp) with h5355 | h5355
                                  · linarith only [h5129, h5355, hlam]
                                  · linarith only [h5128, h5355, hlam]
                                · linarith only [h2, h5354, hlam]
                              · have p5145_0 := h5145c.1
                                have p5145_1 := h5145c.2.1
                                have p5145_2 := h5145c.2.2.1
                                have p5145_3 := h5145c.2.2.2
                                linarith only [hlam, p5145_0]
            · linarith only [h5, h5128, h6, hc12, hc25, hlam, hphi]
          · linarith only [h4, h5127, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 11076000 in
set_option maxHeartbeats 11076000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s5 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5362 | h5362
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5363 | h5363
      · linarith only [h4, h5, h5363, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5365 | h5365
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5366 | h5366
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5367 | h5367
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5368 | h5368
              · linarith only [h0, h5, h5368, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5370 | h5370
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5371 | h5371
                  · linarith only [h5363, h5365, h5371, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5373 | h5373
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5374 | h5374
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5375 | h5375
                        · linarith only [h0, h1, h5, h5363, h5367, h5373, h5375, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5377 | h5377
                          · linarith only [h0, h5, h5367, h5375, h5377, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h4, h5, h5373, h5375, h5377, hc23, hc34, hlam, hphi]
                      · linarith only [h5366, h5368, h5370, h5374, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · linarith only [h5363, h5365, h5373, hc13, hc34, hlam, hphi]
                · linarith only [h5, h5362, h5370, hc12, hc24, hlam, hphi]
            · linarith only [h4, h5, h5367, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h5365, h5366, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5385 | h5385
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5386 | h5386
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5387 | h5387
              · linarith only [h0, h5, h5387, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5389 | h5389
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5390 | h5390
                  · linarith only [h1, h5363, h5390, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5392 | h5392
                    · linarith only [h1, h5365, h5392, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5394 | h5394
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5395 | h5395
                        · linarith only [h0, h1, h5, h5363, h5386, h5395, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5397 | h5397
                          · linarith only [h3, h4, h5, h5365, h5395, h5397, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5399 | h5399
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5400 | h5400
                              · rcases h1bigk with h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c | h5401c
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5389, hc01, hlam, hphi, ht0b, ht5b, p5401_1, u5ehi2]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  rcases p5401_3 (m.d 0 1) (by simp) with h5404 | h5404
                                  · rcases p5401_3 (m.d 1 2) (by simp) with h5405 | h5405
                                    · linarith only [h0, h5405, hlam]
                                    · linarith only [h5386, h5405, hlam]
                                  · linarith only [h5404, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5387, h5389, h5399, hc01, hlam, hphi, ht0b, ht5b, p5401_1, u5ehi4]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  rcases p5401_3 (m.d 0 1) (by simp) with h5410 | h5410
                                  · rcases p5401_3 (m.d 1 2) (by simp) with h5411 | h5411
                                    · linarith only [h0, h5411, hlam]
                                    · linarith only [h5389, h5411, hlam]
                                  · linarith only [h5410, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h0, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h0, h5, h5395, hc13, hc34, hlam, hphi, p5401_1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5387, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h0, h5, h5395, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5401_1, u5ehi1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h1, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5386, hlam, p5401_1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5390, hlam, p5401_1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5392, hlam, p5401_1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h2, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h2, h5386, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5401_1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  rcases p5401_3 (m.d 0 1) (by simp) with h5427 | h5427
                                  · rcases p5401_3 (m.d 1 2) (by simp) with h5428 | h5428
                                    · linarith only [h5387, h5428, hlam]
                                    · linarith only [h5386, h5428, hlam]
                                  · linarith only [h1, h5427, hlam]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h2, h5389, h5399, hc01, hlam, hphi, ht0b, ht5b, p5401_1, u5ehi4]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h3, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5389, hlam, p5401_1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h3, h5, h5362, h5386, h5395, hc23, hc34, hlam, hphi, p5401_1]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [h5394, hlam, p5401_0]
                                · have p5401_0 := h5401c.1
                                  have p5401_1 := h5401c.2.1
                                  have p5401_2 := h5401c.2.2.1
                                  have p5401_3 := h5401c.2.2.2
                                  linarith only [hlam, p5401_0]
                              · linarith only [h0, h5, h5389, h5395, h5399, h5400, hlam]
                            · linarith only [h0, h5, h5389, h5399, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · linarith only [h5, h5362, h5385, h5387, h5389, h5394, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h5, h5362, h5389, hc12, hc24, hlam, hphi]
            · linarith only [h4, h5, h5386, hc12, hc24, hlam, hphi]
          · linarith only [h5, h5362, h5385, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5445 | h5445
      · linarith only [h4, h5, h5445, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5447 | h5447
        · linarith only [h4, h5362, h5447, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5449 | h5449
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5450 | h5450
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5451 | h5451
              · linarith only [h0, h5, h5451, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5453 | h5453
                · linarith only [h0, h5362, h5453, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5455 | h5455
                  · linarith only [h1, h5445, h5455, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5457 | h5457
                    · linarith only [h1, h5447, h5457, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5459 | h5459
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5460 | h5460
                        · linarith only [h0, h1, h5, h5445, h5450, h5460, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5462 | h5462
                          · linarith only [h4, h5362, h5447, h5462, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5464 | h5464
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5465 | h5465
                              · rcases h1bigk with h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c | h5466c
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  rcases p5466_3 (m.d 0 1) (by simp) with h5468 | h5468
                                  · rcases p5466_3 (m.d 1 2) (by simp) with h5469 | h5469
                                    · linarith only [h5469, hlam, p5466_0]
                                    · rcases p5466_3 (m.d 1 3) (by simp) with h5471 | h5471
                                      · linarith only [h1, h5471, hlam]
                                      · rcases p5466_3 (m.d 1 4) (by simp) with h5473 | h5473
                                        · linarith only [h2, h5473, hlam]
                                        · linarith only [h5451, h5473, hlam]
                                  · linarith only [h5468, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  rcases p5466_3 (m.d 0 1) (by simp) with h5477 | h5477
                                  · rcases p5466_3 (m.d 1 2) (by simp) with h5478 | h5478
                                    · linarith only [h0, h5478, hlam]
                                    · linarith only [h5450, h5478, hlam]
                                  · linarith only [h5477, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h5459, hc01, hlam, hphi, ht0b, ht5b, p5466_1, u5ehi4]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  rcases p5466_3 (m.d 0 1) (by simp) with h5483 | h5483
                                  · rcases p5466_3 (m.d 1 2) (by simp) with h5484 | h5484
                                    · linarith only [h0, h5484, hlam]
                                    · rcases p5466_3 (m.d 1 3) (by simp) with h5486 | h5486
                                      · linarith only [h1, h5486, hlam]
                                      · rcases p5466_3 (m.d 1 4) (by simp) with h5488 | h5488
                                        · linarith only [h2, h5488, hlam]
                                        · linarith only [h5459, h5488, hlam]
                                  · linarith only [h5483, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h0, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h0, h5362, h5460, h5464, hc13, hc34, hlam, hphi, p5466_1]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h5451, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h5453, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h1, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h5450, hlam, p5466_1]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h5455, hlam, p5466_1]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h5457, hlam, p5466_1]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h2, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h2, h5450, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5466_1]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  rcases p5466_3 (m.d 0 1) (by simp) with h5504 | h5504
                                  · rcases p5466_3 (m.d 1 2) (by simp) with h5505 | h5505
                                    · linarith only [h5451, h5505, hlam]
                                    · linarith only [h5450, h5505, hlam]
                                  · linarith only [h1, h5504, hlam]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h2, h5, h5450, h5453, h5460, hc23, hc34, hlam, hphi, p5466_1]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h3, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h3, h5450, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5466_1]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  rcases p5466_3 (m.d 0 1) (by simp) with h5513 | h5513
                                  · rcases p5466_3 (m.d 1 2) (by simp) with h5514 | h5514
                                    · linarith only [h5453, h5514, hlam]
                                    · linarith only [h5450, h5514, hlam]
                                  · linarith only [h1, h5513, hlam]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [h5459, hlam, p5466_0]
                                · have p5466_0 := h5466c.1
                                  have p5466_1 := h5466c.2.1
                                  have p5466_2 := h5466c.2.2.1
                                  have p5466_3 := h5466c.2.2.2
                                  linarith only [hlam, p5466_0]
                              · linarith only [h0, h5, h5450, h5460, h5465, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h2, h5, h5459, h5464, hlam]
                      · linarith only [h5445, h5449, h5450, h5451, h5459, hc23, hc34, hlam, hphi]
            · linarith only [h4, h5, h5450, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5524 | h5524
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5525 | h5525
              · linarith only [h0, h5, h5525, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5527 | h5527
                · linarith only [h0, h5362, h5527, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5529 | h5529
                  · linarith only [h1, h5445, h5529, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5531 | h5531
                    · linarith only [h1, h4, h5, h5445, h5447, h5449, h5531, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5533 | h5533
                      · linarith only [h2, h5449, h5533, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5535 | h5535
                        · linarith only [h0, h5, h5449, h5524, h5535, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5537 | h5537
                          · linarith only [h0, h5, h5447, h5449, h5524, h5537, hc03, hc45, hlam, hphi, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5539 | h5539
                            · linarith only [h4, h5, h5449, h5535, h5539, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h5, h5524, h5539, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h5524, hc12, hc24, hlam, hphi]

end R2N4
