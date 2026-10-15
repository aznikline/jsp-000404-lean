import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14754000 in
set_option maxHeartbeats 14754000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s4_x0_x0_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h4610 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h4611 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4612 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4613 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4614 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4615 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4616 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4989 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5097 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h5098 | h5098
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5099 | h5099
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5100 | h5100
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5101 | h5101
        · linarith only [h4610, h4616, h5101, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5103 | h5103
          · linarith only [h4610, h4989, h5103, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5105 | h5105
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5106 | h5106
              · linarith only [h0, h4610, h4611, h4616, h5098, h5105, h5106, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5108 | h5108
                · linarith only [h4610, h4989, h5098, h5108, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5110 | h5110
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5111 | h5111
                    · rcases h0bigk with h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c | h5112c
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [hlam, p5112_0]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h0, hlam, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        rcases p5112_3 (m.d 0 1) (by simp) with h5115 | h5115
                        · rcases p5112_3 (m.d 0 2) (by simp) with h5116 | h5116
                          · rcases p5112_3 (m.d 0 3) (by simp) with h5117 | h5117
                            · linarith only [h4610, h5117, hlam]
                            · rcases p5112_3 (m.d 0 4) (by simp) with h5119 | h5119
                              · linarith only [h4611, h5119, hlam]
                              · linarith only [h4616, h5119, hlam]
                          · linarith only [h4613, h5116, hlam]
                        · linarith only [h4610, h5115, hlam]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h0, h5097, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        rcases p5112_3 (m.d 0 1) (by simp) with h5125 | h5125
                        · rcases p5112_3 (m.d 0 2) (by simp) with h5126 | h5126
                          · rcases p5112_3 (m.d 0 3) (by simp) with h5127 | h5127
                            · linarith only [h4610, h5127, hlam]
                            · rcases p5112_3 (m.d 0 4) (by simp) with h5129 | h5129
                              · linarith only [h4611, h5129, hlam]
                              · linarith only [h5097, h5129, hlam]
                          · linarith only [h4615, h5126, hlam]
                        · linarith only [h4612, h5125, hlam]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4610, h5098, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5112_1, u0elo1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [hlam, p5112_0]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        rcases p5112_3 (m.d 0 1) (by simp) with h5136 | h5136
                        · linarith only [h0, h5136, hlam]
                        · linarith only [h4610, h5136, hlam]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4611, h5099, h5110, hc45, hlam, hphi, ht0b, ht5b, p5112_1, u0elo1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        rcases p5112_3 (m.d 0 1) (by simp) with h5140 | h5140
                        · linarith only [h0, h5140, hlam]
                        · linarith only [h4612, h5140, hlam]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4610, hlam, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4613, hlam, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [hlam, p5112_0]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4616, hlam, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4989, hlam, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4611, hlam, p5112_0]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4614, hlam, p5112_0]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        rcases p5112_3 (m.d 0 1) (by simp) with h5150 | h5150
                        · rcases p5112_3 (m.d 0 2) (by simp) with h5151 | h5151
                          · rcases p5112_3 (m.d 0 3) (by simp) with h5152 | h5152
                            · linarith only [h4616, h5152, hlam]
                            · rcases p5112_3 (m.d 0 4) (by simp) with h5154 | h5154
                              · rcases p5112_3 (m.d 0 5) (by simp) with h5155 | h5155
                                · linarith only [h5097, h5155, hlam]
                                · linarith only [h4989, h5155, hlam]
                              · linarith only [h4616, h5154, hlam]
                          · linarith only [h4613, h5151, hlam]
                        · linarith only [h4610, h5150, hlam]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [hlam, p5112_0]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        rcases p5112_3 (m.d 0 1) (by simp) with h5162 | h5162
                        · rcases p5112_3 (m.d 0 2) (by simp) with h5163 | h5163
                          · rcases p5112_3 (m.d 0 3) (by simp) with h5164 | h5164
                            · linarith only [h4616, h5164, hlam]
                            · rcases p5112_3 (m.d 0 4) (by simp) with h5166 | h5166
                              · rcases p5112_3 (m.d 0 5) (by simp) with h5167 | h5167
                                · linarith only [h5097, h5167, hlam]
                                · rcases h2bigk with h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c | h5169c
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h0, hlam, p5169_1]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    rcases p5169_3 (m.d 0 2) (by simp) with h5172 | h5172
                                    · rcases p5169_3 (m.d 1 2) (by simp) with h5173 | h5173
                                      · rcases p5169_3 (m.d 2 3) (by simp) with h5174 | h5174
                                        · linarith only [h5174, hlam, p5169_0]
                                        · rcases p5169_3 (m.d 2 4) (by simp) with h5176 | h5176
                                          · linarith only [h4614, h5176, hlam]
                                          · linarith only [h5106, h5176, hlam]
                                      · linarith only [h5098, h5173, hlam]
                                    · linarith only [h5172, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h5110, hc45, hlam, hphi, ht0b, ht5b, p5169_1, u0elo1]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    rcases p5169_3 (m.d 0 2) (by simp) with h5182 | h5182
                                    · rcases p5169_3 (m.d 1 2) (by simp) with h5183 | h5183
                                      · rcases p5169_3 (m.d 2 3) (by simp) with h5184 | h5184
                                        · linarith only [h4613, h5184, hlam]
                                        · rcases p5169_3 (m.d 2 4) (by simp) with h5186 | h5186
                                          · linarith only [h4614, h5186, hlam]
                                          · linarith only [h5110, h5186, hlam]
                                      · linarith only [h5100, h5183, hlam]
                                    · linarith only [h5182, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h0, h4610, h4611, h4989, h5098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5112_1, p5169_1]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h0, h4610, h4611, h4989, h5098, hlam, p5112_1, p5169_2]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    rcases p5169_3 (m.d 0 2) (by simp) with h5194 | h5194
                                    · linarith only [h0, h5194, hlam]
                                    · linarith only [h4614, h5194, hlam]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h0, h4611, h4612, h5100, hlam, p5112_1, p5169_2]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h4613, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h5098, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h5106, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h5108, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h4614, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h5099, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h4611, h5099, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5169_1, u0elo0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h0, h4611, h5099, hc25, hlam, hphi, ht0b, ht5b, p5169_1, u0elo1]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h4615, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h5100, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h4615, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5169_1, u0elo1]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [h5110, hlam, p5169_0]
                                  · have p5169_0 := h5169c.1
                                    have p5169_1 := h5169c.2.1
                                    have p5169_2 := h5169c.2.2.1
                                    have p5169_3 := h5169c.2.2.2
                                    linarith only [hlam, p5169_0]
                              · linarith only [h5097, h5166, hlam]
                          · linarith only [h4615, h5163, hlam]
                        · linarith only [h4612, h5162, hlam]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4612, hlam, p5112_0]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h4615, hlam, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        rcases p5112_3 (m.d 0 1) (by simp) with h5218 | h5218
                        · rcases p5112_3 (m.d 0 2) (by simp) with h5219 | h5219
                          · rcases p5112_3 (m.d 0 3) (by simp) with h5220 | h5220
                            · linarith only [h4989, h5220, hlam]
                            · rcases p5112_3 (m.d 0 4) (by simp) with h5222 | h5222
                              · rcases p5112_3 (m.d 0 5) (by simp) with h5223 | h5223
                                · rcases h2bigk with h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c | h5224c
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h0, hlam, p5224_1]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    rcases p5224_3 (m.d 0 2) (by simp) with h5227 | h5227
                                    · rcases p5224_3 (m.d 1 2) (by simp) with h5228 | h5228
                                      · rcases p5224_3 (m.d 2 3) (by simp) with h5229 | h5229
                                        · linarith only [h5229, hlam, p5224_0]
                                        · rcases p5224_3 (m.d 2 4) (by simp) with h5231 | h5231
                                          · linarith only [h4614, h5231, hlam]
                                          · linarith only [h5106, h5231, hlam]
                                      · linarith only [h5098, h5228, hlam]
                                    · linarith only [h5227, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h5110, hc45, hlam, hphi, ht0b, ht5b, p5224_1, u0elo1]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    rcases p5224_3 (m.d 0 2) (by simp) with h5237 | h5237
                                    · rcases p5224_3 (m.d 1 2) (by simp) with h5238 | h5238
                                      · rcases p5224_3 (m.d 2 3) (by simp) with h5239 | h5239
                                        · linarith only [h4613, h5239, hlam]
                                        · rcases p5224_3 (m.d 2 4) (by simp) with h5241 | h5241
                                          · linarith only [h4614, h5241, hlam]
                                          · linarith only [h5110, h5241, hlam]
                                      · linarith only [h5100, h5238, hlam]
                                    · linarith only [h5237, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h0, h4610, h4612, h5098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5112_1, p5224_1]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h0, h4610, h4611, h5097, h5098, hlam, p5112_1, p5224_2]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    rcases p5224_3 (m.d 0 2) (by simp) with h5249 | h5249
                                    · linarith only [h0, h5249, hlam]
                                    · linarith only [h4614, h5249, hlam]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    rcases p5224_3 (m.d 0 2) (by simp) with h5252 | h5252
                                    · linarith only [h0, h5252, hlam]
                                    · linarith only [h4615, h5252, hlam]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h4613, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h5098, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h5106, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h5108, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h4614, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h5099, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h4614, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5224_1, u0elo1]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h4611, h5099, hc25, hlam, hphi, ht0b, ht5b, p5224_1, u0elo0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h4615, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h5100, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h4615, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5224_1, u0elo1]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [h5110, hlam, p5224_0]
                                  · have p5224_0 := h5224c.1
                                    have p5224_1 := h5224c.2.1
                                    have p5224_2 := h5224c.2.2.1
                                    have p5224_3 := h5224c.2.2.2
                                    linarith only [hlam, p5224_0]
                                · linarith only [h4989, h5223, hlam]
                              · linarith only [h4616, h5222, hlam]
                          · linarith only [h4613, h5219, hlam]
                        · linarith only [h4610, h5218, hlam]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [h5097, hlam, p5112_1]
                      · have p5112_0 := h5112c.1
                        have p5112_1 := h5112c.2.1
                        have p5112_2 := h5112c.2.2.1
                        have p5112_3 := h5112c.2.2.2
                        linarith only [hlam, p5112_0]
                    · linarith only [h4616, h5097, h5111, hlam]
                  · linarith only [h4611, h5105, h5110, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5278 | h5278
              · linarith only [h4616, h5097, h5098, h5101, h5105, h5278, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5280 | h5280
                · linarith only [h4989, h5097, h5098, h5101, h5105, h5280, hc05, hlam, hphi, ht0b, ht5b, u0elo3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5282 | h5282
                  · linarith only [h4614, h5098, h5101, h5105, h5282, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5284 | h5284
                    · rcases h0bigk with h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c | h5285c
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [hlam, p5285_0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h0, hlam, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        rcases p5285_3 (m.d 0 1) (by simp) with h5288 | h5288
                        · rcases p5285_3 (m.d 0 2) (by simp) with h5289 | h5289
                          · rcases p5285_3 (m.d 0 3) (by simp) with h5290 | h5290
                            · linarith only [h4610, h5290, hlam]
                            · rcases p5285_3 (m.d 0 4) (by simp) with h5292 | h5292
                              · linarith only [h4611, h5292, hlam]
                              · linarith only [h4616, h5292, hlam]
                          · linarith only [h4613, h5289, hlam]
                        · linarith only [h4610, h5288, hlam]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h0, h5097, h5098, h5101, h5105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h0, h5097, h5098, h5101, h5105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4610, h5098, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5285_1, u0elo1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [hlam, p5285_0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        rcases p5285_3 (m.d 0 1) (by simp) with h5301 | h5301
                        · linarith only [h0, h5301, hlam]
                        · linarith only [h4610, h5301, hlam]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h5097, h5098, h5101, h5105, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5285_1, u0elo1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h5097, h5098, h5101, h5105, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5285_1, u0elo1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4610, hlam, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4613, hlam, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [hlam, p5285_0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4616, hlam, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4989, hlam, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4611, hlam, p5285_0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4614, hlam, p5285_0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        rcases p5285_3 (m.d 0 1) (by simp) with h5313 | h5313
                        · rcases p5285_3 (m.d 0 2) (by simp) with h5314 | h5314
                          · rcases p5285_3 (m.d 0 3) (by simp) with h5315 | h5315
                            · linarith only [h4616, h5315, hlam]
                            · rcases p5285_3 (m.d 0 4) (by simp) with h5317 | h5317
                              · rcases p5285_3 (m.d 0 5) (by simp) with h5318 | h5318
                                · linarith only [h5097, h5318, hlam]
                                · linarith only [h4989, h5318, hlam]
                              · linarith only [h4616, h5317, hlam]
                          · linarith only [h4613, h5314, hlam]
                        · linarith only [h4610, h5313, hlam]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [hlam, p5285_0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4611, h5097, h5098, h5101, h5105, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5285_1, u0elo0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4612, hlam, p5285_0]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h4615, hlam, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        rcases p5285_3 (m.d 0 1) (by simp) with h5328 | h5328
                        · rcases p5285_3 (m.d 0 2) (by simp) with h5329 | h5329
                          · rcases p5285_3 (m.d 0 3) (by simp) with h5330 | h5330
                            · linarith only [h4989, h5330, hlam]
                            · rcases p5285_3 (m.d 0 4) (by simp) with h5332 | h5332
                              · rcases p5285_3 (m.d 0 5) (by simp) with h5333 | h5333
                                · rcases h2bigk with h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c | h5334c
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h0, hlam, p5334_1]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    rcases p5334_3 (m.d 0 2) (by simp) with h5337 | h5337
                                    · rcases p5334_3 (m.d 1 2) (by simp) with h5338 | h5338
                                      · rcases p5334_3 (m.d 2 3) (by simp) with h5339 | h5339
                                        · linarith only [h5339, hlam, p5334_0]
                                        · rcases p5334_3 (m.d 2 4) (by simp) with h5341 | h5341
                                          · linarith only [h4614, h5341, hlam]
                                          · linarith only [h5278, h5341, hlam]
                                      · linarith only [h5098, h5338, hlam]
                                    · linarith only [h5337, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    rcases p5334_3 (m.d 0 2) (by simp) with h5346 | h5346
                                    · rcases p5334_3 (m.d 1 2) (by simp) with h5347 | h5347
                                      · rcases p5334_3 (m.d 2 3) (by simp) with h5348 | h5348
                                        · linarith only [h4613, h5348, hlam]
                                        · rcases p5334_3 (m.d 2 4) (by simp) with h5350 | h5350
                                          · linarith only [h5350, hlam, p5334_0]
                                          · rcases p5334_3 (m.d 2 5) (by simp) with h5352 | h5352
                                            · linarith only [h4615, h5352, hlam]
                                            · linarith only [h5282, h5352, hlam]
                                      · linarith only [h5099, h5347, hlam]
                                    · linarith only [h5346, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    rcases p5334_3 (m.d 0 2) (by simp) with h5357 | h5357
                                    · rcases p5334_3 (m.d 1 2) (by simp) with h5358 | h5358
                                      · rcases p5334_3 (m.d 2 3) (by simp) with h5359 | h5359
                                        · linarith only [h4613, h5359, hlam]
                                        · rcases p5334_3 (m.d 2 4) (by simp) with h5361 | h5361
                                          · linarith only [h4614, h5361, hlam]
                                          · rcases p5334_3 (m.d 2 5) (by simp) with h5363 | h5363
                                            · linarith only [h5363, hlam, p5334_0]
                                            · rcases h3bigk with h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c | h5365c
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5098, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5285_1, p5365_1, u0elo4]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h0, h4612, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5285_1, p5365_1]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h4616, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h4989, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h4610, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5101, h5105, hc23, hc45, hlam, hphi, ht34, p5365_1]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5101, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5103, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h4613, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5098, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5278, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5280, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                rcases p5365_3 (m.d 0 3) (by simp) with h5381 | h5381
                                                · linarith only [h5381, hlam, p5365_0]
                                                · rcases p5365_3 (m.d 1 3) (by simp) with h5383 | h5383
                                                  · linarith only [h5101, h5383, hlam]
                                                  · rcases p5365_3 (m.d 2 3) (by simp) with h5385 | h5385
                                                    · linarith only [h5278, h5385, hlam]
                                                    · rcases p5365_3 (m.d 3 4) (by simp) with h5387 | h5387
                                                      · rcases p5365_3 (m.d 3 5) (by simp) with h5388 | h5388
                                                        · linarith only [h5284, h5388, hlam]
                                                        · linarith only [h4989, h5388, hlam]
                                                      · linarith only [h5387, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                rcases p5365_3 (m.d 0 3) (by simp) with h5392 | h5392
                                                · linarith only [h4616, h5392, hlam]
                                                · linarith only [h4610, h5392, hlam]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                rcases p5365_3 (m.d 0 3) (by simp) with h5395 | h5395
                                                · linarith only [h4616, h5395, hlam]
                                                · linarith only [h4613, h5395, hlam]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h4989, hc03, hc34, hlam, hphi, p5285_1, p5365_1]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                rcases p5365_3 (m.d 0 3) (by simp) with h5400 | h5400
                                                · linarith only [h5400, hlam, p5365_0]
                                                · rcases p5365_3 (m.d 1 3) (by simp) with h5402 | h5402
                                                  · linarith only [h5103, h5402, hlam]
                                                  · rcases p5365_3 (m.d 2 3) (by simp) with h5404 | h5404
                                                    · linarith only [h5280, h5404, hlam]
                                                    · rcases p5365_3 (m.d 3 4) (by simp) with h5406 | h5406
                                                      · rcases p5365_3 (m.d 3 5) (by simp) with h5407 | h5407
                                                        · rcases h5bigk with h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c | h5408c
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [hlam, p5408_0]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            rcases p5408_3 (m.d 0 5) (by simp) with h5410 | h5410
                                                            · rcases p5408_3 (m.d 1 5) (by simp) with h5411 | h5411
                                                              · linarith only [h4612, h5411, hlam]
                                                              · rcases p5408_3 (m.d 2 5) (by simp) with h5413 | h5413
                                                                · linarith only [h4615, h5413, hlam]
                                                                · rcases p5408_3 (m.d 3 5) (by simp) with h5415 | h5415
                                                                  · rcases p5408_3 (m.d 4 5) (by simp) with h5416 | h5416
                                                                    · linarith only [h5097, h5416, hlam]
                                                                    · linarith only [h5105, h5416, hlam]
                                                                  · linarith only [h5103, h5415, hlam]
                                                            · linarith only [h4612, h5410, hlam]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            rcases p5408_3 (m.d 0 5) (by simp) with h5421 | h5421
                                                            · rcases p5408_3 (m.d 1 5) (by simp) with h5422 | h5422
                                                              · linarith only [h4612, h5422, hlam]
                                                              · linarith only [h5100, h5422, hlam]
                                                            · linarith only [h4615, h5421, hlam]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h4989, hlam, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h0, h4611, h5097, h5098, h5101, h5105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h4612, hlam, p5408_0]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [hlam, p5408_0]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h0, h4612, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5103, hlam, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5105, hlam, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h4615, hlam, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5100, hlam, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [hlam, p5408_0]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5280, hlam, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5282, hlam, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [hc03, hc35, hlam, hphi, p5285_1, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            rcases p5408_3 (m.d 0 5) (by simp) with h5439 | h5439
                                                            · linarith only [h4989, h5439, hlam]
                                                            · linarith only [h4612, h5439, hlam]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            rcases p5408_3 (m.d 0 5) (by simp) with h5442 | h5442
                                                            · linarith only [h4989, h5442, hlam]
                                                            · linarith only [h4615, h5442, hlam]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [hlam, p5408_0]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5098, h5101, h5105, h5284, hc23, hc34, hlam, hphi, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5097, hlam, p5408_0]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h0, h4611, h5097, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h0, h4611, h5097, h5278, h5282, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5408_1]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [h5284, hlam, p5408_0]
                                                          · have p5408_0 := h5408c.1
                                                            have p5408_1 := h5408c.2.1
                                                            have p5408_2 := h5408c.2.2.1
                                                            have p5408_3 := h5408c.2.2.2
                                                            linarith only [hlam, p5408_0]
                                                        · linarith only [h5407, hlam, p5365_0]
                                                      · linarith only [h4616, h5406, hlam]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                rcases p5365_3 (m.d 0 3) (by simp) with h5454 | h5454
                                                · linarith only [h4989, h5454, hlam]
                                                · linarith only [h4610, h5454, hlam]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                rcases p5365_3 (m.d 0 3) (by simp) with h5457 | h5457
                                                · linarith only [h4989, h5457, hlam]
                                                · linarith only [h4613, h5457, hlam]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [h5284, hlam, p5365_0]
                                              · have p5365_0 := h5365c.1
                                                have p5365_1 := h5365c.2.1
                                                have p5365_2 := h5365c.2.2.1
                                                have p5365_3 := h5365c.2.2.2
                                                linarith only [hlam, p5365_0]
                                      · linarith only [h5100, h5358, hlam]
                                    · linarith only [h5357, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h0, h4610, h4612, h5098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5285_1, p5334_1]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h0, h4610, h4611, h5097, h5098, hlam, p5285_1, p5334_2]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h0, h4611, h5097, h5099, h5105, hlam, p5334_2]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    rcases p5334_3 (m.d 0 2) (by simp) with h5468 | h5468
                                    · linarith only [h0, h5468, hlam]
                                    · linarith only [h4615, h5468, hlam]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h4613, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h5098, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h5278, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h5280, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h4614, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h5099, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h4611, h5097, h5099, h5105, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5334_1, u0elo0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h5282, hlam, p5334_1]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h4615, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h5100, hlam, p5334_0]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h0, h4612, h5100, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5334_1, u0elo1]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [h0, h4611, h5097, h5100, h5105, hc24, hlam, hphi, ht0b, ht45, ht5b, p5334_1, u0elo1]
                                  · have p5334_0 := h5334c.1
                                    have p5334_1 := h5334c.2.1
                                    have p5334_2 := h5334c.2.2.1
                                    have p5334_3 := h5334c.2.2.2
                                    linarith only [hlam, p5334_0]
                                · linarith only [h4989, h5333, hlam]
                              · linarith only [h4616, h5332, hlam]
                          · linarith only [h4613, h5329, hlam]
                        · linarith only [h4610, h5328, hlam]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [h5097, hlam, p5285_1]
                      · have p5285_0 := h5285c.1
                        have p5285_1 := h5285c.2.1
                        have p5285_2 := h5285c.2.2.1
                        have p5285_3 := h5285c.2.2.2
                        linarith only [hlam, p5285_0]
                    · linarith only [h0, h4610, h4611, h4616, h5097, h5098, h5284, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h4615, h5100, hlam]
    · linarith only [h0, h4614, h5099, hlam]
  · linarith only [h0, h4613, h5098, hlam]

end R2N4
