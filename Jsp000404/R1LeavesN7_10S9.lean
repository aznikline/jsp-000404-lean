import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x1_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4281 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4724 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h5137 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1 := hg1
  rcases m.htr 0 4 5 (by decide) (by decide) with h5138 | h5138
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5139 | h5139
    · linarith only [h0, h2, h5139, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5141 | h5141
      · linarith only [h0, h4281, h5141, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5143 | h5143
        · linarith only [h0, h4724, h5143, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5145 | h5145
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5146 | h5146
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5147 | h5147
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5148 | h5148
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5149 | h5149
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5150 | h5150
                    · rcases h2bigk with h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c | h5151c
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h4724, h5149, hc12, hc24, hlam, hphi, p5151_1]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h2, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h4281, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h4724, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h0, hlam, p5151_1]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h5139, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h5141, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h5143, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        rcases p5151_3 (m.d 0 2) (by simp) with h5162 | h5162
                        · linarith only [h5162, hlam, p5151_0]
                        · rcases p5151_3 (m.d 1 2) (by simp) with h5164 | h5164
                          · linarith only [h5139, h5164, hlam]
                          · rcases p5151_3 (m.d 2 3) (by simp) with h5166 | h5166
                            · rcases p5151_3 (m.d 2 4) (by simp) with h5167 | h5167
                              · linarith only [h5147, h5167, hlam]
                              · linarith only [h4281, h5167, hlam]
                            · linarith only [h5166, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        rcases p5151_3 (m.d 0 2) (by simp) with h5171 | h5171
                        · linarith only [h2, h5171, hlam]
                        · linarith only [h0, h5171, hlam]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h4281, hc02, hc23, hlam, hphi, p5151_1]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h0, h4724, hc12, hc23, hlam, hphi, p5151_1]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        rcases p5151_3 (m.d 0 2) (by simp) with h5177 | h5177
                        · linarith only [h5177, hlam, p5151_0]
                        · rcases p5151_3 (m.d 1 2) (by simp) with h5179 | h5179
                          · linarith only [h5141, h5179, hlam]
                          · rcases p5151_3 (m.d 2 3) (by simp) with h5181 | h5181
                            · rcases p5151_3 (m.d 2 4) (by simp) with h5182 | h5182
                              · rcases p5151_3 (m.d 2 5) (by simp) with h5183 | h5183
                                · linarith only [h5149, h5183, hlam]
                                · linarith only [h4724, h5183, hlam]
                              · linarith only [h5182, hlam, p5151_0]
                            · linarith only [h2, h5181, hlam]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        rcases p5151_3 (m.d 0 2) (by simp) with h5188 | h5188
                        · linarith only [h4281, h5188, hlam]
                        · linarith only [h0, h5188, hlam]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h5147, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h0, h4724, hc12, hc24, hlam, hphi, p5151_1]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        rcases p5151_3 (m.d 0 2) (by simp) with h5194 | h5194
                        · linarith only [h5194, hlam, p5151_0]
                        · rcases p5151_3 (m.d 1 2) (by simp) with h5196 | h5196
                          · linarith only [h5143, h5196, hlam]
                          · rcases p5151_3 (m.d 2 3) (by simp) with h5198 | h5198
                            · rcases p5151_3 (m.d 2 4) (by simp) with h5199 | h5199
                              · rcases p5151_3 (m.d 2 5) (by simp) with h5200 | h5200
                                · rcases h4bigk with h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c | h5201c
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5145, h5150, hc04, hc45, hlam, hphi, ht0b, ht5b, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h4281, hlam, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h4281, h5147, h5150, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    rcases p5201_3 (m.d 0 4) (by simp) with h5206 | h5206
                                    · rcases p5201_3 (m.d 1 4) (by simp) with h5207 | h5207
                                      · linarith only [h1, h5207, hlam]
                                      · linarith only [h5146, h5207, hlam]
                                    · linarith only [h5206, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h1, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5141, hlam, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5150, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h0, h4281, h5147, hc12, hc23, hlam, hphi, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5141, h5147, hc12, hc23, hlam, hphi, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5147, h5150, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    rcases p5201_3 (m.d 0 4) (by simp) with h5220 | h5220
                                    · linarith only [h4281, h5220, hlam]
                                    · linarith only [h5138, h5220, hlam]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5137, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5145, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5147, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5137, hc03, hc45, hlam, hphi, ht0b, ht5b, p5201_1]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5138, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5146, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5149, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [h5150, hlam, p5201_0]
                                  · have p5201_0 := h5201c.1
                                    have p5201_1 := h5201c.2.1
                                    have p5201_2 := h5201c.2.2.1
                                    have p5201_3 := h5201c.2.2.2
                                    linarith only [hlam, p5201_0]
                                · linarith only [h5200, hlam, p5151_0]
                              · linarith only [h4281, h5199, hlam]
                            · linarith only [h2, h5198, hlam]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        rcases p5151_3 (m.d 0 2) (by simp) with h5236 | h5236
                        · linarith only [h4724, h5236, hlam]
                        · linarith only [h0, h5236, hlam]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h5148, hlam, p5151_0]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [h5149, hlam, p5151_1]
                      · have p5151_0 := h5151c.1
                        have p5151_1 := h5151c.2.1
                        have p5151_2 := h5151c.2.2.1
                        have p5151_3 := h5151c.2.2.2
                        linarith only [hlam, p5151_0]
                    · rcases h2bigk with h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c | h5242c
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h2, hc12, hc23, hlam, hphi, p5242_1]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h2, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h4281, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h4724, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h0, hlam, p5242_1]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h5139, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h5141, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h5143, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        rcases p5242_3 (m.d 0 2) (by simp) with h5253 | h5253
                        · linarith only [h5253, hlam, p5242_0]
                        · rcases p5242_3 (m.d 1 2) (by simp) with h5255 | h5255
                          · linarith only [h5139, h5255, hlam]
                          · rcases p5242_3 (m.d 2 3) (by simp) with h5257 | h5257
                            · rcases p5242_3 (m.d 2 4) (by simp) with h5258 | h5258
                              · linarith only [h5147, h5258, hlam]
                              · linarith only [h4281, h5258, hlam]
                            · linarith only [h5257, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        rcases p5242_3 (m.d 0 2) (by simp) with h5262 | h5262
                        · linarith only [h2, h5262, hlam]
                        · linarith only [h0, h5262, hlam]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h1, h4281, h5146, h5150, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5242_1]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h4724, hc02, hc23, hlam, hphi, p5242_1]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        rcases p5242_3 (m.d 0 2) (by simp) with h5268 | h5268
                        · linarith only [h5268, hlam, p5242_0]
                        · rcases p5242_3 (m.d 1 2) (by simp) with h5270 | h5270
                          · linarith only [h5141, h5270, hlam]
                          · rcases p5242_3 (m.d 2 3) (by simp) with h5272 | h5272
                            · rcases p5242_3 (m.d 2 4) (by simp) with h5273 | h5273
                              · rcases p5242_3 (m.d 2 5) (by simp) with h5274 | h5274
                                · linarith only [h5149, h5274, hlam]
                                · linarith only [h4724, h5274, hlam]
                              · linarith only [h5273, hlam, p5242_0]
                            · linarith only [h2, h5272, hlam]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        rcases p5242_3 (m.d 0 2) (by simp) with h5279 | h5279
                        · linarith only [h4281, h5279, hlam]
                        · linarith only [h0, h5279, hlam]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h5147, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h0, h4724, hc12, hc24, hlam, hphi, p5242_1]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        rcases p5242_3 (m.d 0 2) (by simp) with h5285 | h5285
                        · linarith only [h5285, hlam, p5242_0]
                        · rcases p5242_3 (m.d 1 2) (by simp) with h5287 | h5287
                          · linarith only [h5143, h5287, hlam]
                          · rcases p5242_3 (m.d 2 3) (by simp) with h5289 | h5289
                            · rcases p5242_3 (m.d 2 4) (by simp) with h5290 | h5290
                              · rcases p5242_3 (m.d 2 5) (by simp) with h5291 | h5291
                                · rcases h4bigk with h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c | h5292c
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5137, h5146, h5150, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h4281, hlam, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    rcases p5292_3 (m.d 0 4) (by simp) with h5296 | h5296
                                    · rcases p5292_3 (m.d 1 4) (by simp) with h5297 | h5297
                                      · linarith only [h1, h5297, hlam]
                                      · linarith only [h5145, h5297, hlam]
                                    · linarith only [h5137, h5296, hlam]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h2, h5137, h5150, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h1, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5141, hlam, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h1, h5150, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h0, h4281, h5147, hc12, hc23, hlam, hphi, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5141, h5147, hc12, hc23, hlam, hphi, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    rcases p5292_3 (m.d 0 4) (by simp) with h5310 | h5310
                                    · linarith only [h4281, h5310, hlam]
                                    · linarith only [h5137, h5310, hlam]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5147, h5150, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5137, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5145, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5147, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5150, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5138, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5146, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h5149, hlam, p5292_0]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [h1, h5146, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p5292_1]
                                  · have p5292_0 := h5292c.1
                                    have p5292_1 := h5292c.2.1
                                    have p5292_2 := h5292c.2.2.1
                                    have p5292_3 := h5292c.2.2.2
                                    linarith only [hlam, p5292_0]
                                · linarith only [h5291, hlam, p5242_0]
                              · linarith only [h4281, h5290, hlam]
                            · linarith only [h2, h5289, hlam]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        rcases p5242_3 (m.d 0 2) (by simp) with h5327 | h5327
                        · linarith only [h4724, h5327, hlam]
                        · linarith only [h0, h5327, hlam]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h5148, hlam, p5242_0]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [h5149, hlam, p5242_1]
                      · have p5242_0 := h5242c.1
                        have p5242_1 := h5242c.2.1
                        have p5242_2 := h5242c.2.2.1
                        have p5242_3 := h5242c.2.2.2
                        linarith only [hlam, p5242_0]
                  · linarith only [h1, h4281, h5146, h5149, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5334 | h5334
                  · linarith only [h5147, h5148, h5334, hlam]
                  · linarith only [h0, h1, h2, h4281, h5137, h5146, h5148, h5334, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h2, h5137, h5147, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5338 | h5338
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5339 | h5339
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5340 | h5340
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5341 | h5341
                    · linarith only [h5145, h5146, h5341, hlam]
                    · rcases h2bigk with h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h2, hc12, hc23, hlam, hphi, p5343_1]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h2, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h4281, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h4724, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h0, hlam, p5343_1]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h5139, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h5141, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h5143, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        rcases p5343_3 (m.d 0 2) (by simp) with h5354 | h5354
                        · linarith only [h5354, hlam, p5343_0]
                        · rcases p5343_3 (m.d 1 2) (by simp) with h5356 | h5356
                          · linarith only [h5139, h5356, hlam]
                          · rcases p5343_3 (m.d 2 3) (by simp) with h5358 | h5358
                            · rcases p5343_3 (m.d 2 4) (by simp) with h5359 | h5359
                              · linarith only [h5338, h5359, hlam]
                              · linarith only [h4281, h5359, hlam]
                            · linarith only [h5358, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        rcases p5343_3 (m.d 0 2) (by simp) with h5363 | h5363
                        · linarith only [h2, h5363, hlam]
                        · linarith only [h0, h5363, hlam]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h4281, hc02, hc23, hlam, hphi, p5343_1]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h0, h4724, hc12, hc23, hlam, hphi, p5343_1]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        rcases p5343_3 (m.d 0 2) (by simp) with h5369 | h5369
                        · linarith only [h5369, hlam, p5343_0]
                        · rcases p5343_3 (m.d 1 2) (by simp) with h5371 | h5371
                          · linarith only [h5141, h5371, hlam]
                          · rcases p5343_3 (m.d 2 3) (by simp) with h5373 | h5373
                            · rcases p5343_3 (m.d 2 4) (by simp) with h5374 | h5374
                              · rcases p5343_3 (m.d 2 5) (by simp) with h5375 | h5375
                                · linarith only [h5340, h5375, hlam]
                                · linarith only [h4724, h5375, hlam]
                              · linarith only [h5374, hlam, p5343_0]
                            · linarith only [h2, h5373, hlam]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        rcases p5343_3 (m.d 0 2) (by simp) with h5380 | h5380
                        · linarith only [h4281, h5380, hlam]
                        · linarith only [h0, h5380, hlam]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h5338, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h4724, h5138, h5141, h5146, hc12, hc24, hlam, hphi, p5343_1]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        rcases p5343_3 (m.d 0 2) (by simp) with h5386 | h5386
                        · linarith only [h5386, hlam, p5343_0]
                        · rcases p5343_3 (m.d 1 2) (by simp) with h5388 | h5388
                          · linarith only [h5143, h5388, hlam]
                          · rcases p5343_3 (m.d 2 3) (by simp) with h5390 | h5390
                            · rcases p5343_3 (m.d 2 4) (by simp) with h5391 | h5391
                              · rcases p5343_3 (m.d 2 5) (by simp) with h5392 | h5392
                                · rcases h4bigk with h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c | h5393c
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h2, h5137, h5141, hc12, hc23, hlam, hphi, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h4281, hlam, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    rcases p5393_3 (m.d 0 4) (by simp) with h5397 | h5397
                                    · rcases p5393_3 (m.d 1 4) (by simp) with h5398 | h5398
                                      · linarith only [h1, h5398, hlam]
                                      · linarith only [h5145, h5398, hlam]
                                    · linarith only [h5137, h5397, hlam]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h2, h5137, h5141, h5146, hc12, hc23, hlam, hphi, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h1, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5141, hlam, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5138, h5146, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5146, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h0, h4281, h5338, hc12, hc23, hlam, hphi, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5141, h5338, hc12, hc23, hlam, hphi, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    rcases p5393_3 (m.d 0 4) (by simp) with h5411 | h5411
                                    · linarith only [h4281, h5411, hlam]
                                    · linarith only [h5137, h5411, hlam]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5141, h5146, h5338, hc12, hc23, hlam, hphi, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5137, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5145, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5338, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5341, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5138, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5138, h5141, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h5340, hlam, p5393_0]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [h4281, h5138, h5338, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5393_1]
                                  · have p5393_0 := h5393c.1
                                    have p5393_1 := h5393c.2.1
                                    have p5393_2 := h5393c.2.2.1
                                    have p5393_3 := h5393c.2.2.2
                                    linarith only [hlam, p5393_0]
                                · linarith only [h5392, hlam, p5343_0]
                              · linarith only [h4281, h5391, hlam]
                            · linarith only [h2, h5390, hlam]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        rcases p5343_3 (m.d 0 2) (by simp) with h5428 | h5428
                        · linarith only [h4724, h5428, hlam]
                        · linarith only [h0, h5428, hlam]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h5339, hlam, p5343_0]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [h5340, hlam, p5343_1]
                      · have p5343_0 := h5343c.1
                        have p5343_1 := h5343c.2.1
                        have p5343_2 := h5343c.2.2.1
                        have p5343_3 := h5343c.2.2.2
                        linarith only [hlam, p5343_0]
                  · linarith only [h4281, h5138, h5340, hlam]
                · linarith only [h4281, h5138, h5141, h5146, h5338, h5339, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h2, h5137, h5138, h5141, h5146, h5338, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5437 | h5437
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5438 | h5438
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5439 | h5439
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5440 | h5440
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5441 | h5441
                    · rcases h2bigk with h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c | h5442c
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h2, hc12, hc23, hlam, hphi, p5442_1]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h2, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h4281, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h4724, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h0, hlam, p5442_1]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h5139, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h5141, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h5143, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        rcases p5442_3 (m.d 0 2) (by simp) with h5453 | h5453
                        · linarith only [h5453, hlam, p5442_0]
                        · rcases p5442_3 (m.d 1 2) (by simp) with h5455 | h5455
                          · linarith only [h5139, h5455, hlam]
                          · rcases p5442_3 (m.d 2 3) (by simp) with h5457 | h5457
                            · rcases p5442_3 (m.d 2 4) (by simp) with h5458 | h5458
                              · linarith only [h5438, h5458, hlam]
                              · linarith only [h4281, h5458, hlam]
                            · linarith only [h5457, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        rcases p5442_3 (m.d 0 2) (by simp) with h5462 | h5462
                        · linarith only [h2, h5462, hlam]
                        · linarith only [h0, h5462, hlam]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h4281, hc02, hc23, hlam, hphi, p5442_1]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h0, h4724, hc12, hc23, hlam, hphi, p5442_1]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        rcases p5442_3 (m.d 0 2) (by simp) with h5468 | h5468
                        · linarith only [h5468, hlam, p5442_0]
                        · rcases p5442_3 (m.d 1 2) (by simp) with h5470 | h5470
                          · linarith only [h5141, h5470, hlam]
                          · rcases p5442_3 (m.d 2 3) (by simp) with h5472 | h5472
                            · rcases p5442_3 (m.d 2 4) (by simp) with h5473 | h5473
                              · rcases p5442_3 (m.d 2 5) (by simp) with h5474 | h5474
                                · linarith only [h5440, h5474, hlam]
                                · linarith only [h4724, h5474, hlam]
                              · linarith only [h5473, hlam, p5442_0]
                            · linarith only [h2, h5472, hlam]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        rcases p5442_3 (m.d 0 2) (by simp) with h5479 | h5479
                        · linarith only [h4281, h5479, hlam]
                        · linarith only [h0, h5479, hlam]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h5438, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h0, h4724, hc12, hc24, hlam, hphi, p5442_1]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        rcases p5442_3 (m.d 0 2) (by simp) with h5485 | h5485
                        · linarith only [h5485, hlam, p5442_0]
                        · rcases p5442_3 (m.d 1 2) (by simp) with h5487 | h5487
                          · linarith only [h5143, h5487, hlam]
                          · rcases p5442_3 (m.d 2 3) (by simp) with h5489 | h5489
                            · rcases p5442_3 (m.d 2 4) (by simp) with h5490 | h5490
                              · rcases p5442_3 (m.d 2 5) (by simp) with h5491 | h5491
                                · rcases h4bigk with h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h4281, h5141, h5438, hc12, hc23, hlam, hphi, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h4281, hlam, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h4281, h5139, h5145, h5438, hc12, hc23, hlam, hphi, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    rcases p5492_3 (m.d 0 4) (by simp) with h5497 | h5497
                                    · rcases p5492_3 (m.d 1 4) (by simp) with h5498 | h5498
                                      · linarith only [h1, h5498, hlam]
                                      · linarith only [h5437, h5498, hlam]
                                    · linarith only [h5497, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h1, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5141, hlam, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5145, hlam, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h0, h4281, h5438, hc12, hc23, hlam, hphi, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5141, h5438, hc12, hc23, hlam, hphi, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5139, h5145, h5438, hc12, hc23, hlam, hphi, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    rcases p5492_3 (m.d 0 4) (by simp) with h5511 | h5511
                                    · linarith only [h4281, h5511, hlam]
                                    · linarith only [h5138, h5511, hlam]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5137, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5137, h5437, hc04, hc45, hlam, hphi, ht0b, ht5b, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5438, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h2, h5137, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5492_1]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5138, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5437, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5440, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [h5441, hlam, p5492_0]
                                  · have p5492_0 := h5492c.1
                                    have p5492_1 := h5492c.2.1
                                    have p5492_2 := h5492c.2.2.1
                                    have p5492_3 := h5492c.2.2.2
                                    linarith only [hlam, p5492_0]
                                · linarith only [h5491, hlam, p5442_0]
                              · linarith only [h4281, h5490, hlam]
                            · linarith only [h2, h5489, hlam]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        rcases p5442_3 (m.d 0 2) (by simp) with h5527 | h5527
                        · linarith only [h4724, h5527, hlam]
                        · linarith only [h0, h5527, hlam]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h5439, hlam, p5442_0]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [h5440, hlam, p5442_1]
                      · have p5442_0 := h5442c.1
                        have p5442_1 := h5442c.2.1
                        have p5442_2 := h5442c.2.2.1
                        have p5442_3 := h5442c.2.2.2
                        linarith only [hlam, p5442_0]
                    · linarith only [h1, h5139, h5145, h5437, h5441, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1, h4281, h5437, h5440, hlam]
                · linarith only [h2, h5137, h5139, h5145, h5439, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h2, h5137, h5438, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5537 | h5537
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5538 | h5538
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5539 | h5539
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5540 | h5540
                    · linarith only [h2, h5137, h5139, h5145, h5437, h5540, hc12, hc23, hlam, hphi]
                    · linarith only [h4281, h5138, h5139, h5145, h5540, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h2, h4281, h5137, h5138, h5539, hc12, hc23, hlam, hphi]
                · linarith only [h2, h5137, h5139, h5145, h5538, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h2, h5137, h5138, h5139, h5145, h5437, h5537, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5546 | h5546
    · linarith only [h0, h2, h5546, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5548 | h5548
      · linarith only [h0, h4281, h5548, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5550 | h5550
        · linarith only [h0, h4724, h5550, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5552 | h5552
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5553 | h5553
            · linarith only [h1, h5138, h5553, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5555 | h5555
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5556 | h5556
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5557 | h5557
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5558 | h5558
                    · linarith only [h0, h2, h4281, h5137, h5138, h5558, hc12, hc23, hlam, hphi]
                    · rcases h2bigk with h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c | h5560c
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h4281, h5138, h5557, hc12, hc24, hlam, hphi, p5560_1]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h2, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h4281, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h4724, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h0, hlam, p5560_1]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h5546, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h5548, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h5550, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        rcases p5560_3 (m.d 0 2) (by simp) with h5571 | h5571
                        · linarith only [h5571, hlam, p5560_0]
                        · rcases p5560_3 (m.d 1 2) (by simp) with h5573 | h5573
                          · linarith only [h5546, h5573, hlam]
                          · rcases p5560_3 (m.d 2 3) (by simp) with h5575 | h5575
                            · rcases p5560_3 (m.d 2 4) (by simp) with h5576 | h5576
                              · linarith only [h5555, h5576, hlam]
                              · linarith only [h4281, h5576, hlam]
                            · linarith only [h5575, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        rcases p5560_3 (m.d 0 2) (by simp) with h5580 | h5580
                        · linarith only [h2, h5580, hlam]
                        · linarith only [h0, h5580, hlam]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h4281, h5138, h5557, hc02, hc23, hlam, hphi, p5560_1]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h0, h4281, h5138, h5557, hc12, hc23, hlam, hphi, p5560_1]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        rcases p5560_3 (m.d 0 2) (by simp) with h5586 | h5586
                        · linarith only [h5586, hlam, p5560_0]
                        · rcases p5560_3 (m.d 1 2) (by simp) with h5588 | h5588
                          · linarith only [h5548, h5588, hlam]
                          · rcases p5560_3 (m.d 2 3) (by simp) with h5590 | h5590
                            · rcases p5560_3 (m.d 2 4) (by simp) with h5591 | h5591
                              · rcases p5560_3 (m.d 2 5) (by simp) with h5592 | h5592
                                · linarith only [h5557, h5592, hlam]
                                · linarith only [h4724, h5592, hlam]
                              · linarith only [h5591, hlam, p5560_0]
                            · linarith only [h2, h5590, hlam]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        rcases p5560_3 (m.d 0 2) (by simp) with h5597 | h5597
                        · linarith only [h4281, h5597, hlam]
                        · linarith only [h0, h5597, hlam]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h5555, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h0, h4281, h5138, h5557, hc12, hc24, hlam, hphi, p5560_1]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        rcases p5560_3 (m.d 0 2) (by simp) with h5603 | h5603
                        · linarith only [h5603, hlam, p5560_0]
                        · rcases p5560_3 (m.d 1 2) (by simp) with h5605 | h5605
                          · linarith only [h5550, h5605, hlam]
                          · rcases p5560_3 (m.d 2 3) (by simp) with h5607 | h5607
                            · rcases p5560_3 (m.d 2 4) (by simp) with h5608 | h5608
                              · rcases p5560_3 (m.d 2 5) (by simp) with h5609 | h5609
                                · rcases h4bigk with h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c | h5610c
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5138, h5552, hc34, hc45, hlam, hphi, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h4281, hlam, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5138, hc34, hc45, hlam, hphi, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5138, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h1, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5548, hlam, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5553, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h0, h4281, h5555, hc12, hc23, hlam, hphi, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5548, h5555, hc12, hc23, hlam, hphi, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    rcases p5610_3 (m.d 0 4) (by simp) with h5624 | h5624
                                    · linarith only [h4281, h5624, hlam]
                                    · linarith only [h5137, h5624, hlam]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h0, h4724, h5138, h5555, hc12, hc23, hlam, hphi, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5137, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5552, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5555, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5558, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h0, h4281, hc12, hc45, hlam, hphi, ht23, ht34, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5548, hc12, hc45, hlam, hphi, ht23, ht34, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5557, hlam, p5610_0]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [h5555, h5557, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5610_1]
                                  · have p5610_0 := h5610c.1
                                    have p5610_1 := h5610c.2.1
                                    have p5610_2 := h5610c.2.2.1
                                    have p5610_3 := h5610c.2.2.2
                                    linarith only [hlam, p5610_0]
                                · linarith only [h5609, hlam, p5560_0]
                              · linarith only [h4281, h5608, hlam]
                            · linarith only [h2, h5607, hlam]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        rcases p5560_3 (m.d 0 2) (by simp) with h5641 | h5641
                        · linarith only [h4724, h5641, hlam]
                        · linarith only [h0, h5641, hlam]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h5556, hlam, p5560_0]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [h5557, hlam, p5560_1]
                      · have p5560_0 := h5560c.1
                        have p5560_1 := h5560c.2.1
                        have p5560_2 := h5560c.2.2.1
                        have p5560_3 := h5560c.2.2.2
                        linarith only [hlam, p5560_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5647 | h5647
                    · linarith only [h0, h4281, h5552, h5557, h5647, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h2bigk with h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c | h5649c
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h4281, hc12, hc24, hlam, hphi, p5649_1]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h2, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h4281, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h4724, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h0, hlam, p5649_1]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h5546, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h5548, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h5550, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        rcases p5649_3 (m.d 0 2) (by simp) with h5660 | h5660
                        · linarith only [h5660, hlam, p5649_0]
                        · rcases p5649_3 (m.d 1 2) (by simp) with h5662 | h5662
                          · linarith only [h5546, h5662, hlam]
                          · rcases p5649_3 (m.d 2 3) (by simp) with h5664 | h5664
                            · rcases p5649_3 (m.d 2 4) (by simp) with h5665 | h5665
                              · linarith only [h5555, h5665, hlam]
                              · linarith only [h4281, h5665, hlam]
                            · linarith only [h5664, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        rcases p5649_3 (m.d 0 2) (by simp) with h5669 | h5669
                        · linarith only [h2, h5669, hlam]
                        · linarith only [h0, h5669, hlam]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h4281, hc02, hc23, hlam, hphi, p5649_1]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h0, h4724, hc12, hc23, hlam, hphi, p5649_1]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h0, h5557, hc12, hc45, hlam, hphi, ht23, ht34, p5649_1]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h5557, hc12, hc45, hlam, hphi, ht23, ht34, p5649_1]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h5555, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h5557, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        rcases p5649_3 (m.d 0 2) (by simp) with h5680 | h5680
                        · linarith only [h5680, hlam, p5649_0]
                        · rcases p5649_3 (m.d 1 2) (by simp) with h5682 | h5682
                          · linarith only [h5550, h5682, hlam]
                          · rcases p5649_3 (m.d 2 3) (by simp) with h5684 | h5684
                            · rcases p5649_3 (m.d 2 4) (by simp) with h5685 | h5685
                              · linarith only [h5557, h5685, hlam]
                              · linarith only [h4281, h5685, hlam]
                            · linarith only [h2, h5684, hlam]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        rcases p5649_3 (m.d 0 2) (by simp) with h5689 | h5689
                        · linarith only [h4724, h5689, hlam]
                        · linarith only [h0, h5689, hlam]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h5556, hlam, p5649_0]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [h0, h4281, hc12, hc25, hlam, hphi, p5649_1]
                      · have p5649_0 := h5649c.1
                        have p5649_1 := h5649c.2.1
                        have p5649_2 := h5649c.2.2.1
                        have p5649_3 := h5649c.2.2.2
                        linarith only [hlam, p5649_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5695 | h5695
                  · linarith only [h0, h4281, h5138, h5555, h5556, h5695, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5697 | h5697
                    · linarith only [h0, h1, h4281, h4724, h5552, h5555, h5556, h5695, h5697, hc12, hc35, hlam, hphi, ht23]
                    · rcases h2bigk with h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c | h5699c
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h2, h5556, h5697, hc12, hc45, hlam, hphi, ht23, ht34, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h2, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h4281, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h4724, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h0, hlam, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5546, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5548, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5550, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5556, h5697, hc02, hc45, hlam, hphi, ht23, ht34, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5556, h5697, hc12, hc45, hlam, hphi, ht23, ht34, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h4281, h5556, h5697, hc04, hc45, hlam, hphi, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5556, hlam, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h0, h5555, h5556, h5697, hc12, hc45, hlam, hphi, ht23, ht34, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5555, h5556, h5697, hc12, hc45, hlam, hphi, ht23, ht34, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5555, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h5695, hlam, p5699_0]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        rcases p5699_3 (m.d 0 2) (by simp) with h5720 | h5720
                        · linarith only [h5720, hlam, p5699_0]
                        · rcases p5699_3 (m.d 1 2) (by simp) with h5722 | h5722
                          · linarith only [h5550, h5722, hlam]
                          · rcases p5699_3 (m.d 2 3) (by simp) with h5724 | h5724
                            · linarith only [h5556, h5724, hlam]
                            · linarith only [h2, h5724, hlam]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        rcases p5699_3 (m.d 0 2) (by simp) with h5727 | h5727
                        · linarith only [h4724, h5727, hlam]
                        · linarith only [h0, h5727, hlam]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h0, h2, hc12, hc25, hlam, hphi, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [h0, h4281, h5556, h5697, hc12, hc45, hlam, hphi, ht23, ht34, p5699_1]
                      · have p5699_0 := h5699c.1
                        have p5699_1 := h5699c.2.1
                        have p5699_2 := h5699c.2.2.1
                        have p5699_3 := h5699c.2.2.2
                        linarith only [hlam, p5699_0]
              · linarith only [h2, h5137, h5555, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5734 | h5734
            · linarith only [h1, h5138, h5734, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5736 | h5736
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5737 | h5737
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5738 | h5738
                  · linarith only [h5137, h5138, h5546, h5552, h5738, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5740 | h5740
                    · linarith only [h4281, h5137, h5738, h5740, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h2bigk with h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c | h5742c
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h2, hc12, hc23, hlam, hphi, p5742_1]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h2, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h4281, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h4724, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h0, hlam, p5742_1]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h5546, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h5548, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h5550, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        rcases p5742_3 (m.d 0 2) (by simp) with h5753 | h5753
                        · linarith only [h5753, hlam, p5742_0]
                        · rcases p5742_3 (m.d 1 2) (by simp) with h5755 | h5755
                          · linarith only [h5546, h5755, hlam]
                          · rcases p5742_3 (m.d 2 3) (by simp) with h5757 | h5757
                            · rcases p5742_3 (m.d 2 4) (by simp) with h5758 | h5758
                              · linarith only [h5736, h5758, hlam]
                              · linarith only [h4281, h5758, hlam]
                            · linarith only [h5757, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        rcases p5742_3 (m.d 0 2) (by simp) with h5762 | h5762
                        · linarith only [h2, h5762, hlam]
                        · linarith only [h0, h5762, hlam]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h4281, hc02, hc23, hlam, hphi, p5742_1]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h0, h4724, hc12, hc23, hlam, hphi, p5742_1]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h0, h5738, hc12, hc45, hlam, hphi, ht23, ht34, p5742_1]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h5738, hc12, hc45, hlam, hphi, ht23, ht34, p5742_1]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h5736, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h5738, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        rcases p5742_3 (m.d 0 2) (by simp) with h5773 | h5773
                        · linarith only [h5773, hlam, p5742_0]
                        · rcases p5742_3 (m.d 1 2) (by simp) with h5775 | h5775
                          · linarith only [h5550, h5775, hlam]
                          · rcases p5742_3 (m.d 2 3) (by simp) with h5777 | h5777
                            · rcases p5742_3 (m.d 2 4) (by simp) with h5778 | h5778
                              · linarith only [h5738, h5778, hlam]
                              · linarith only [h4281, h5778, hlam]
                            · linarith only [h2, h5777, hlam]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        rcases p5742_3 (m.d 0 2) (by simp) with h5782 | h5782
                        · linarith only [h4724, h5782, hlam]
                        · linarith only [h0, h5782, hlam]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h5737, hlam, p5742_0]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [h0, h4281, hc12, hc25, hlam, hphi, p5742_1]
                      · have p5742_0 := h5742c.1
                        have p5742_1 := h5742c.2.1
                        have p5742_2 := h5742c.2.2.1
                        have p5742_3 := h5742c.2.2.2
                        linarith only [hlam, p5742_0]
                · linarith only [h2, h5137, h5546, h5552, h5737, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h2, h5137, h5736, hlam]

end R2N4
