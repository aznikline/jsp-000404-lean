import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10766000 in
set_option maxHeartbeats 10766000 in
theorem r1l7_21_15_H_I_L_I_s1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_15_H_I_L_I_s2 m hb1 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h5094 | h5094
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5095 | h5095
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5096 | h5096
        · linarith only [h0, h2, h5096, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5098 | h5098
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5099 | h5099
            · linarith only [h1, h2, h5099, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5101 | h5101
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5102 | h5102
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5103 | h5103
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5104 | h5104
                    · linarith only [h0, h2, h5096, h5098, h5104, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5106 | h5106
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5107 | h5107
                        · linarith only [h0, h2, h5099, h5103, h5104, h5107, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h5103, h5107, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h5098, h5103, h5104, h5106, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h5095, h5096, h5103, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h5101, h5102, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5113 | h5113
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5114 | h5114
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5115 | h5115
                    · linarith only [h0, h2, h5096, h5115, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5117 | h5117
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5118 | h5118
                        · linarith only [h0, h1, h2, h5099, h5101, h5114, h5118, hc23, hc35, hlam, hphi]
                        · linarith only [h0, h2, h5114, h5118, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h5098, h5114, h5115, h5117, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h5095, h5096, h5114, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h5098, h5113, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5124 | h5124
            · linarith only [h1, h2, h5124, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5126 | h5126
              · linarith only [h5095, h5098, h5126, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5128 | h5128
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5129 | h5129
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5130 | h5130
                    · linarith only [h0, h2, h5096, h5130, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5132 | h5132
                      · linarith only [h0, h5098, h5132, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5134 | h5134
                        · linarith only [h1, h2, h5124, h5134, hlam]
                        · linarith only [h0, h2, h5129, h5134, hc23, hc34, hlam, hphi]
                  · linarith only [h5095, h5098, h5129, hc12, hc25, hlam, hphi]
                · linarith only [h2, h5094, h5128, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5139 | h5139
        · linarith only [h0, h2, h5139, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5141 | h5141
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5142 | h5142
            · linarith only [h1, h2, h5142, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5144 | h5144
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5145 | h5145
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5146 | h5146
                  · linarith only [h0, h2, h5095, h5146, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5148 | h5148
                    · linarith only [h0, h2, h5139, h5148, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5150 | h5150
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5151 | h5151
                        · linarith only [h1, h2, h5095, h5142, h5151, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5153 | h5153
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5154 | h5154
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5155 | h5155
                              · linarith only [h1, h2, h5146, h5150, h5151, h5155, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5157 | h5157
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5158 | h5158
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5159 | h5159
                                    · rcases h1bigk with h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c | h5160c
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h2, h5148, h5150, h5155, h5157, h5159, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h2, h5146, h5148, h5150, h5155, h5157, h5159, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h2, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h2, h5148, h5155, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h0, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5146, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5148, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h0, h2, h5148, h5155, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h1, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h1, h2, h5148, h5155, hc12, hc34, hlam, hphi, ht23, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5151, hlam, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h1, h2, h5148, h5150, h5155, h5157, h5159, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5148, h5155, hc01, hc34, hlam, hphi, ht12, ht23, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5148, h5150, h5155, h5157, h5159, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5146, h5148, h5150, h5155, h5157, h5159, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        rcases p5160_3 (m.d 0 1) (by simp) with h5180 | h5180
                                        · linarith only [h2, h5180, hlam]
                                        · linarith only [h5094, h5180, hlam]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5094, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5150, hlam, p5160_1]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5153, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [h5154, hlam, p5160_0]
                                      · have p5160_0 := h5160c.1
                                        have p5160_1 := h5160c.2.1
                                        have p5160_2 := h5160c.2.2.1
                                        have p5160_3 := h5160c.2.2.2
                                        linarith only [hlam, p5160_0]
                                    · linarith only [h1, h2, h5146, h5148, h5155, h5159, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h2, h5146, h5148, h5150, h5154, h5157, h5158, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h5095, h5144, h5150, h5157, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h2, h5146, h5150, h5154, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h2, h5144, h5146, h5150, h5153, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1, h2, h5095, h5141, h5148, h5150, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h5095, h5141, h5145, hlam]
              · linarith only [h5095, h5141, h5144, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5196 | h5196
            · linarith only [h1, h2, h5196, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5198 | h5198
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5199 | h5199
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5200 | h5200
                  · linarith only [h0, h2, h5095, h5200, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5202 | h5202
                    · linarith only [h0, h5139, h5202, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5204 | h5204
                      · linarith only [h0, h5141, h5204, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5206 | h5206
                        · linarith only [h1, h2, h5196, h5202, h5206, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5208 | h5208
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5209 | h5209
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5210 | h5210
                              · linarith only [h0, h2, h5206, h5210, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5212 | h5212
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5213 | h5213
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5214 | h5214
                                    · rcases h1bigk with h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h2, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h2, h5202, h5210, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h0, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5200, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5202, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5204, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h1, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h1, h2, h5202, h5210, hc12, hc34, hlam, hphi, ht23, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5206, hlam, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h1, h2, h5202, h5204, h5210, hc12, hc34, hlam, hphi, ht23, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5202, h5210, hc01, hc34, hlam, hphi, ht12, ht23, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5202, h5210, hc12, hc34, hlam, hphi, ht23, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5200, h5202, h5210, hc12, hc34, hlam, hphi, ht23, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5202, h5204, h5210, hc12, hc34, hlam, hphi, ht23, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5094, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5094, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5215_1]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5208, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [h5209, hlam, p5215_0]
                                      · have p5215_0 := h5215c.1
                                        have p5215_1 := h5215c.2.1
                                        have p5215_2 := h5215c.2.2.1
                                        have p5215_3 := h5215c.2.2.2
                                        linarith only [hlam, p5215_0]
                                    · linarith only [h1, h2, h5202, h5208, h5210, h5214, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h1, h2, h5094, h5202, h5208, h5209, h5213, hc05, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h1, h2, h5208, h5212, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1, h2, h5209, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h1, h2, h5198, h5200, h5206, h5208, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h2, h5198, h5199, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5247 | h5247
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5248 | h5248
                  · linarith only [h0, h5095, h5248, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5250 | h5250
                    · linarith only [h0, h5139, h5250, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5252 | h5252
                      · linarith only [h0, h5141, h5252, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5254 | h5254
                        · linarith only [h0, h1, h2, h5196, h5198, h5254, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5256 | h5256
                          · linarith only [h1, h5198, h5256, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5258 | h5258
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5259 | h5259
                              · linarith only [h0, h2, h5254, h5259, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5261 | h5261
                                · linarith only [h5198, h5259, h5261, hc03, hc34, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5263 | h5263
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5264 | h5264
                                    · rcases h1bigk with h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c | h5265c
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h2, h5250, h5259, hc12, hc34, hlam, hphi, ht23, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h2, h5250, h5259, hc13, hc34, hlam, hphi, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h2, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h2, h5250, h5259, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h0, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5248, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5250, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5252, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h1, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h1, h2, h5250, h5259, hc12, hc34, hlam, hphi, ht23, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5254, hlam, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5256, hlam, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5250, h5259, hc01, hc34, hlam, hphi, ht12, ht23, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5250, h5259, hc12, hc34, hlam, hphi, ht23, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5248, h5250, h5259, hc12, hc34, hlam, hphi, ht23, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5248, h5250, h5256, h5259, hc12, hc34, hlam, hphi, ht23, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5094, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5094, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h2, h5094, h5248, h5250, h5259, hc12, hc34, hlam, hphi, ht23, p5265_1]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [h5258, hlam, p5265_0]
                                      · have p5265_0 := h5265c.1
                                        have p5265_1 := h5265c.2.1
                                        have p5265_2 := h5265c.2.2.1
                                        have p5265_3 := h5265c.2.2.2
                                        linarith only [hlam, p5265_0]
                                    · linarith only [h0, h2, h5250, h5259, h5264, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h2, h5094, h5250, h5258, h5263, hlam]
                            · linarith only [h2, h5094, h5248, h5256, h5258, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h5094, h5247, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5295 | h5295
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5296 | h5296
        · linarith only [h0, h2, h5296, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5298 | h5298
          · linarith only [h0, h5094, h5298, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5300 | h5300
            · linarith only [h1, h2, h5300, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5302 | h5302
              · linarith only [h0, h5094, h5295, h5302, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5304 | h5304
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5305 | h5305
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5306 | h5306
                    · linarith only [h0, h2, h5296, h5306, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5308 | h5308
                      · linarith only [h0, h5094, h5298, h5308, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5310 | h5310
                        · linarith only [h0, h2, h5300, h5305, h5306, h5310, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h5305, h5310, hc23, hc34, hlam, hphi]
                  · linarith only [h5295, h5296, h5305, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5314 | h5314
                  · linarith only [h0, h2, h5304, h5314, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h5295, h5304, h5314, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5317 | h5317
        · linarith only [h1, h2, h5295, h5317, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5319 | h5319
          · linarith only [h1, h5094, h5295, h5319, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5321 | h5321
            · linarith only [h1, h2, h5321, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5323 | h5323
              · linarith only [h1, h5094, h5323, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5325 | h5325
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5326 | h5326
                  · linarith only [h0, h2, h5295, h5326, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5328 | h5328
                    · linarith only [h0, h5094, h5317, h5325, h5328, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5330 | h5330
                      · linarith only [h1, h5094, h5319, h5326, h5330, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5332 | h5332
                        · linarith only [h1, h2, h5321, h5325, h5332, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5334 | h5334
                          · linarith only [h1, h2, h5295, h5323, h5332, h5334, hc02, hc34, hlam, hphi, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5336 | h5336
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5337 | h5337
                              · linarith only [h0, h5094, h5332, h5336, h5337, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5339 | h5339
                                · linarith only [h1, h5094, h5326, h5334, h5339, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5341 | h5341
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5342 | h5342
                                    · rcases h1bigk with h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c | h5343c
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5094, h5336, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5094, h5326, h5328, h5336, hc12, hc24, hlam, hphi, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h2, hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5094, hlam, p5343_0]
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
                                        linarith only [h5326, hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5328, hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5330, hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h1, hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h1, h5094, h5328, h5336, hc12, hc24, hlam, hphi, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5332, hlam, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5334, hlam, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5328, hc01, hc24, hlam, hphi, ht12, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5328, hc12, hc24, hlam, hphi, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5326, h5332, hc12, hc34, hlam, hphi, ht23, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h1, h5094, h5326, h5332, hc12, hc34, hlam, hphi, ht23, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h1, h5326, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5330, hc12, hc25, hlam, hphi, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5326, h5334, h5342, hc12, hc34, hlam, hphi, ht23, p5343_1]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [h5336, hlam, p5343_0]
                                      · have p5343_0 := h5343c.1
                                        have p5343_1 := h5343c.2.1
                                        have p5343_2 := h5343c.2.2.1
                                        have p5343_3 := h5343c.2.2.2
                                        linarith only [hlam, p5343_0]
                                    · linarith only [h1, h2, h5326, h5328, h5337, h5342, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h5094, h5325, h5326, h5328, h5336, h5341, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h2, h5326, h5336, hc12, hc45, hlam, hphi, ht23, ht34]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5372 | h5372
                  · linarith only [h0, h2, h5325, h5372, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5374 | h5374
                    · linarith only [h1, h2, h5325, h5372, h5374, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5376 | h5376
                      · linarith only [h1, h2, h5319, h5325, h5372, h5376, hc02, hc45, hlam, hphi, ht23, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5378 | h5378
                        · linarith only [h1, h2, h5325, h5378, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5380 | h5380
                          · linarith only [h1, h2, h5323, h5325, h5380, hc03, hc45, hlam, hphi, ht34]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5382 | h5382
                            · linarith only [h0, h2, h5325, h5378, h5382, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2, h5372, h5382, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
