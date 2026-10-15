import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h5073 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h5074 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h5075 | h5075
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5076 | h5076
    · linarith only [h1, h5076, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5078 | h5078
      · linarith only [h1, h4553, h5078, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5080 | h5080
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5081 | h5081
          · linarith only [h2, h5073, h5078, h5080, h5081, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5083 | h5083
            · linarith only [h1, h4553, h5073, h5083, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5085 | h5085
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5086 | h5086
                · rcases h0bigk with h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c | h5087c
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h0, h5074, h5085, hc01, hc45, hlam, hphi, ht0b, ht5b, p5087_1]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5090 | h5090
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5091 | h5091
                      · linarith only [h0, h5091, hlam]
                      · linarith only [h4, h5091, hlam]
                    · linarith only [h1, h5090, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5095 | h5095
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5096 | h5096
                      · linarith only [h0, h5096, hlam]
                      · linarith only [h5, h5096, hlam]
                    · linarith only [h2, h5095, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5100 | h5100
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5101 | h5101
                      · linarith only [h0, h5101, hlam]
                      · linarith only [h5101, h6, hlam]
                    · linarith only [h3, h5100, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h0, hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5107 | h5107
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5108 | h5108
                      · rcases p5087_3 (m.d 0 3) (by simp) with h5109 | h5109
                        · linarith only [h4, h5109, hlam]
                        · rcases p5087_3 (m.d 0 4) (by simp) with h5111 | h5111
                          · linarith only [h5, h5111, hlam]
                          · linarith only [h5111, h7, hlam]
                      · linarith only [h4, h5108, hlam]
                    · linarith only [h1, h5107, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5116 | h5116
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5117 | h5117
                      · rcases p5087_3 (m.d 0 3) (by simp) with h5118 | h5118
                        · linarith only [h4, h5118, hlam]
                        · rcases p5087_3 (m.d 0 4) (by simp) with h5120 | h5120
                          · linarith only [h5, h5120, hlam]
                          · rcases p5087_3 (m.d 0 5) (by simp) with h5122 | h5122
                            · linarith only [h5122, h6, hlam]
                            · rcases h2bigk with h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c | h5124c
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5074, h5085, hc02, hc45, hlam, hphi, ht0b, ht5b, p5124_1]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                rcases p5124_3 (m.d 0 2) (by simp) with h5127 | h5127
                                · rcases p5124_3 (m.d 1 2) (by simp) with h5128 | h5128
                                  · linarith only [h0, h5128, hlam]
                                  · linarith only [h5073, h5128, hlam]
                                · linarith only [h5127, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                rcases p5124_3 (m.d 0 2) (by simp) with h5132 | h5132
                                · rcases p5124_3 (m.d 1 2) (by simp) with h5133 | h5133
                                  · linarith only [h0, h5133, hlam]
                                  · linarith only [h5074, h5133, hlam]
                                · linarith only [h5132, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                rcases p5124_3 (m.d 0 2) (by simp) with h5137 | h5137
                                · rcases p5124_3 (m.d 1 2) (by simp) with h5138 | h5138
                                  · linarith only [h0, h5138, hlam]
                                  · linarith only [h5075, h5138, hlam]
                                · linarith only [h5137, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h0, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                rcases p5124_3 (m.d 0 2) (by simp) with h5144 | h5144
                                · rcases p5124_3 (m.d 1 2) (by simp) with h5145 | h5145
                                  · rcases p5124_3 (m.d 2 3) (by simp) with h5146 | h5146
                                    · linarith only [h5146, hlam, p5124_0]
                                    · rcases p5124_3 (m.d 2 4) (by simp) with h5148 | h5148
                                      · linarith only [h5074, h5148, hlam]
                                      · linarith only [h5081, h5148, hlam]
                                  · linarith only [h5145, hlam, p5124_0]
                                · linarith only [h4, h5144, hlam]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h0, h5085, hc01, hc45, hlam, hphi, ht0b, ht5b, p5124_1]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                rcases p5124_3 (m.d 0 2) (by simp) with h5154 | h5154
                                · rcases p5124_3 (m.d 1 2) (by simp) with h5155 | h5155
                                  · rcases p5124_3 (m.d 2 3) (by simp) with h5156 | h5156
                                    · linarith only [h5073, h5156, hlam]
                                    · rcases p5124_3 (m.d 2 4) (by simp) with h5158 | h5158
                                      · linarith only [h5074, h5158, hlam]
                                      · linarith only [h5085, h5158, hlam]
                                  · linarith only [h5155, hlam, p5124_0]
                                · linarith only [h5154, h6, hlam]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h4, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5073, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5081, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5083, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5074, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h0, h2, h5074, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5087_1, p5124_1]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h0, h2, h5074, h5083, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5087_1, p5124_1]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h6, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5075, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h0, h5072, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5087_1, p5124_1]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [h5085, hlam, p5124_0]
                              · have p5124_0 := h5124c.1
                                have p5124_1 := h5124c.2.1
                                have p5124_2 := h5124c.2.2.1
                                have p5124_3 := h5124c.2.2.2
                                linarith only [hlam, p5124_0]
                      · linarith only [h5, h5117, hlam]
                    · linarith only [h2, h5116, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5180 | h5180
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5181 | h5181
                      · rcases p5087_3 (m.d 0 3) (by simp) with h5182 | h5182
                        · linarith only [h4, h5182, hlam]
                        · rcases p5087_3 (m.d 0 4) (by simp) with h5184 | h5184
                          · linarith only [h5, h5184, hlam]
                          · linarith only [h5072, h5184, hlam]
                      · linarith only [h5181, h6, hlam]
                    · linarith only [h3, h5180, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h1, hlam, p5087_1]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h4, hlam, p5087_1]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h7, hlam, p5087_1]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h4553, hlam, p5087_1]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h2, hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h5, hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5196 | h5196
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5197 | h5197
                      · rcases p5087_3 (m.d 0 3) (by simp) with h5198 | h5198
                        · linarith only [h5198, h7, hlam]
                        · rcases p5087_3 (m.d 0 4) (by simp) with h5200 | h5200
                          · rcases p5087_3 (m.d 0 5) (by simp) with h5201 | h5201
                            · linarith only [h5072, h5201, hlam]
                            · linarith only [h4553, h5201, hlam]
                          · linarith only [h5200, h7, hlam]
                      · linarith only [h4, h5197, hlam]
                    · linarith only [h1, h5196, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5208 | h5208
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5209 | h5209
                      · rcases p5087_3 (m.d 0 3) (by simp) with h5210 | h5210
                        · linarith only [h5210, h7, hlam]
                        · rcases p5087_3 (m.d 0 4) (by simp) with h5212 | h5212
                          · rcases p5087_3 (m.d 0 5) (by simp) with h5213 | h5213
                            · linarith only [h5072, h5213, hlam]
                            · rcases h2bigk with h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c | h5215c
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h5074, h5085, hc01, hc45, hlam, hphi, ht0b, ht5b, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                rcases p5215_3 (m.d 0 2) (by simp) with h5218 | h5218
                                · rcases p5215_3 (m.d 1 2) (by simp) with h5219 | h5219
                                  · linarith only [h0, h5219, hlam]
                                  · linarith only [h5073, h5219, hlam]
                                · linarith only [h5218, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                rcases p5215_3 (m.d 0 2) (by simp) with h5223 | h5223
                                · rcases p5215_3 (m.d 1 2) (by simp) with h5224 | h5224
                                  · linarith only [h0, h5224, hlam]
                                  · linarith only [h5074, h5224, hlam]
                                · linarith only [h5223, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                rcases p5215_3 (m.d 0 2) (by simp) with h5228 | h5228
                                · rcases p5215_3 (m.d 1 2) (by simp) with h5229 | h5229
                                  · linarith only [h0, h5229, hlam]
                                  · linarith only [h5075, h5229, hlam]
                                · linarith only [h5228, hlam, p5215_0]
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
                                rcases p5215_3 (m.d 0 2) (by simp) with h5235 | h5235
                                · rcases p5215_3 (m.d 1 2) (by simp) with h5236 | h5236
                                  · rcases p5215_3 (m.d 2 3) (by simp) with h5237 | h5237
                                    · linarith only [h5237, hlam, p5215_0]
                                    · rcases p5215_3 (m.d 2 4) (by simp) with h5239 | h5239
                                      · linarith only [h5074, h5239, hlam]
                                      · linarith only [h5081, h5239, hlam]
                                  · linarith only [h5236, hlam, p5215_0]
                                · linarith only [h4, h5235, hlam]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h5085, hc01, hc45, hlam, hphi, ht0b, ht5b, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                rcases p5215_3 (m.d 0 2) (by simp) with h5245 | h5245
                                · rcases p5215_3 (m.d 1 2) (by simp) with h5246 | h5246
                                  · rcases p5215_3 (m.d 2 3) (by simp) with h5247 | h5247
                                    · linarith only [h5073, h5247, hlam]
                                    · rcases p5215_3 (m.d 2 4) (by simp) with h5249 | h5249
                                      · linarith only [h5074, h5249, hlam]
                                      · linarith only [h5085, h5249, hlam]
                                  · linarith only [h5246, hlam, p5215_0]
                                · linarith only [h5245, h6, hlam]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h4, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5073, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5081, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5083, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5074, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h5074, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h0, h5074, hc01, hc25, hlam, hphi, ht0b, ht5b, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h6, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5075, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5087_1, p5215_1]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [h5085, hlam, p5215_0]
                              · have p5215_0 := h5215c.1
                                have p5215_1 := h5215c.2.1
                                have p5215_2 := h5215c.2.2.1
                                have p5215_3 := h5215c.2.2.2
                                linarith only [hlam, p5215_0]
                          · linarith only [h5072, h5212, hlam]
                      · linarith only [h5209, h6, hlam]
                    · linarith only [h3, h5208, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h3, hlam, p5087_0]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h6, hlam, p5087_1]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    rcases p5087_3 (m.d 0 1) (by simp) with h5274 | h5274
                    · rcases p5087_3 (m.d 0 2) (by simp) with h5275 | h5275
                      · rcases p5087_3 (m.d 0 3) (by simp) with h5276 | h5276
                        · linarith only [h4553, h5276, hlam]
                        · rcases p5087_3 (m.d 0 4) (by simp) with h5278 | h5278
                          · rcases p5087_3 (m.d 0 5) (by simp) with h5279 | h5279
                            · rcases h2bigk with h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h0, h5074, h5085, hc01, hc45, hlam, hphi, ht0b, ht5b, p5280_1]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                rcases p5280_3 (m.d 0 2) (by simp) with h5283 | h5283
                                · rcases p5280_3 (m.d 1 2) (by simp) with h5284 | h5284
                                  · linarith only [h0, h5284, hlam]
                                  · linarith only [h5073, h5284, hlam]
                                · linarith only [h5283, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                rcases p5280_3 (m.d 0 2) (by simp) with h5288 | h5288
                                · rcases p5280_3 (m.d 1 2) (by simp) with h5289 | h5289
                                  · linarith only [h0, h5289, hlam]
                                  · linarith only [h5074, h5289, hlam]
                                · linarith only [h5288, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                rcases p5280_3 (m.d 0 2) (by simp) with h5293 | h5293
                                · rcases p5280_3 (m.d 1 2) (by simp) with h5294 | h5294
                                  · linarith only [h0, h5294, hlam]
                                  · linarith only [h5075, h5294, hlam]
                                · linarith only [h5293, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h0, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                rcases p5280_3 (m.d 0 2) (by simp) with h5300 | h5300
                                · rcases p5280_3 (m.d 1 2) (by simp) with h5301 | h5301
                                  · rcases p5280_3 (m.d 2 3) (by simp) with h5302 | h5302
                                    · linarith only [h5302, hlam, p5280_0]
                                    · rcases p5280_3 (m.d 2 4) (by simp) with h5304 | h5304
                                      · linarith only [h5074, h5304, hlam]
                                      · linarith only [h5081, h5304, hlam]
                                  · linarith only [h5301, hlam, p5280_0]
                                · linarith only [h4, h5300, hlam]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h0, h5085, hc01, hc45, hlam, hphi, ht0b, ht5b, p5280_1]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                rcases p5280_3 (m.d 0 2) (by simp) with h5310 | h5310
                                · rcases p5280_3 (m.d 1 2) (by simp) with h5311 | h5311
                                  · rcases p5280_3 (m.d 2 3) (by simp) with h5312 | h5312
                                    · linarith only [h5073, h5312, hlam]
                                    · rcases p5280_3 (m.d 2 4) (by simp) with h5314 | h5314
                                      · linarith only [h5074, h5314, hlam]
                                      · linarith only [h5085, h5314, hlam]
                                  · linarith only [h5311, hlam, p5280_0]
                                · linarith only [h5310, h6, hlam]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h4, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h5073, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h5081, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h5083, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h5, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h5074, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h0, h5074, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5280_1]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h0, h5074, hc01, hc25, hlam, hphi, ht0b, ht5b, p5280_1]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h6, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h5075, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h0, h5075, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5280_1]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [h5085, hlam, p5280_0]
                              · have p5280_0 := h5280c.1
                                have p5280_1 := h5280c.2.1
                                have p5280_2 := h5280c.2.2.1
                                have p5280_3 := h5280c.2.2.2
                                linarith only [hlam, p5280_0]
                            · linarith only [h4553, h5279, hlam]
                          · linarith only [h5278, h7, hlam]
                      · linarith only [h4, h5275, hlam]
                    · linarith only [h1, h5274, hlam]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [h5072, hlam, p5087_1]
                  · have p5087_0 := h5087c.1
                    have p5087_1 := h5087c.2.1
                    have p5087_2 := h5087c.2.2.1
                    have p5087_3 := h5087c.2.2.2
                    linarith only [hlam, p5087_0]
                · linarith only [h5072, h5086, h7, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5341 | h5341
                · rcases h0bigk with h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c | h5342c
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h2, h5, h5080, h5081, h5085, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    rcases p5342_3 (m.d 0 1) (by simp) with h5345 | h5345
                    · rcases p5342_3 (m.d 0 2) (by simp) with h5346 | h5346
                      · linarith only [h0, h5346, hlam]
                      · linarith only [h4, h5346, hlam]
                    · linarith only [h1, h5345, hlam]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h2, h5080, h5081, h5085, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    rcases p5342_3 (m.d 0 1) (by simp) with h5351 | h5351
                    · rcases p5342_3 (m.d 0 2) (by simp) with h5352 | h5352
                      · linarith only [h0, h5352, hlam]
                      · linarith only [h5352, h6, hlam]
                    · linarith only [h3, h5351, hlam]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h0, hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    rcases p5342_3 (m.d 0 1) (by simp) with h5358 | h5358
                    · rcases p5342_3 (m.d 0 2) (by simp) with h5359 | h5359
                      · rcases p5342_3 (m.d 0 3) (by simp) with h5360 | h5360
                        · linarith only [h4, h5360, hlam]
                        · rcases p5342_3 (m.d 0 4) (by simp) with h5362 | h5362
                          · linarith only [h5, h5362, hlam]
                          · linarith only [h5362, h7, hlam]
                      · linarith only [h4, h5359, hlam]
                    · linarith only [h1, h5358, hlam]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h2, h5080, h5081, h5085, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    rcases p5342_3 (m.d 0 1) (by simp) with h5368 | h5368
                    · rcases p5342_3 (m.d 0 2) (by simp) with h5369 | h5369
                      · rcases p5342_3 (m.d 0 3) (by simp) with h5370 | h5370
                        · linarith only [h4, h5370, hlam]
                        · rcases p5342_3 (m.d 0 4) (by simp) with h5372 | h5372
                          · linarith only [h5, h5372, hlam]
                          · linarith only [h5072, h5372, hlam]
                      · linarith only [h5369, h6, hlam]
                    · linarith only [h3, h5368, hlam]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h1, hlam, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h4, hlam, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h7, hlam, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h4553, hlam, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h2, hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h5, hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    rcases p5342_3 (m.d 0 1) (by simp) with h5384 | h5384
                    · rcases p5342_3 (m.d 0 2) (by simp) with h5385 | h5385
                      · rcases p5342_3 (m.d 0 3) (by simp) with h5386 | h5386
                        · linarith only [h5386, h7, hlam]
                        · rcases p5342_3 (m.d 0 4) (by simp) with h5388 | h5388
                          · rcases p5342_3 (m.d 0 5) (by simp) with h5389 | h5389
                            · linarith only [h5072, h5389, hlam]
                            · linarith only [h4553, h5389, hlam]
                          · linarith only [h5388, h7, hlam]
                      · linarith only [h4, h5385, hlam]
                    · linarith only [h1, h5384, hlam]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h5072, h5081, h5085, h7, hc23, hc34, hlam, hphi, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h3, hlam, p5342_0]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h6, hlam, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    rcases p5342_3 (m.d 0 1) (by simp) with h5399 | h5399
                    · rcases p5342_3 (m.d 0 2) (by simp) with h5400 | h5400
                      · rcases p5342_3 (m.d 0 3) (by simp) with h5401 | h5401
                        · linarith only [h4553, h5401, hlam]
                        · rcases p5342_3 (m.d 0 4) (by simp) with h5403 | h5403
                          · rcases p5342_3 (m.d 0 5) (by simp) with h5404 | h5404
                            · rcases h2bigk with h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c | h5405c
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h0, h5074, h5080, h5081, h5085, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5405_1]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                rcases p5405_3 (m.d 0 2) (by simp) with h5408 | h5408
                                · rcases p5405_3 (m.d 1 2) (by simp) with h5409 | h5409
                                  · linarith only [h0, h5409, hlam]
                                  · linarith only [h5073, h5409, hlam]
                                · linarith only [h5408, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                rcases p5405_3 (m.d 0 2) (by simp) with h5413 | h5413
                                · rcases p5405_3 (m.d 1 2) (by simp) with h5414 | h5414
                                  · linarith only [h0, h5414, hlam]
                                  · linarith only [h5074, h5414, hlam]
                                · linarith only [h5413, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                rcases p5405_3 (m.d 0 2) (by simp) with h5418 | h5418
                                · rcases p5405_3 (m.d 1 2) (by simp) with h5419 | h5419
                                  · linarith only [h0, h5419, hlam]
                                  · linarith only [h5075, h5419, hlam]
                                · linarith only [h5418, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h0, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                rcases p5405_3 (m.d 0 2) (by simp) with h5425 | h5425
                                · rcases p5405_3 (m.d 1 2) (by simp) with h5426 | h5426
                                  · rcases p5405_3 (m.d 2 3) (by simp) with h5427 | h5427
                                    · linarith only [h5427, hlam, p5405_0]
                                    · rcases p5405_3 (m.d 2 4) (by simp) with h5429 | h5429
                                      · linarith only [h5074, h5429, hlam]
                                      · linarith only [h5081, h5429, hlam]
                                  · linarith only [h5426, hlam, p5405_0]
                                · linarith only [h4, h5425, hlam]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                rcases p5405_3 (m.d 0 2) (by simp) with h5434 | h5434
                                · rcases p5405_3 (m.d 1 2) (by simp) with h5435 | h5435
                                  · rcases p5405_3 (m.d 2 3) (by simp) with h5436 | h5436
                                    · linarith only [h5073, h5436, hlam]
                                    · rcases p5405_3 (m.d 2 4) (by simp) with h5438 | h5438
                                      · linarith only [h5438, hlam, p5405_0]
                                      · rcases p5405_3 (m.d 2 5) (by simp) with h5440 | h5440
                                        · linarith only [h5075, h5440, hlam]
                                        · linarith only [h5085, h5440, hlam]
                                  · linarith only [h5435, hlam, p5405_0]
                                · linarith only [h5, h5434, hlam]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                rcases p5405_3 (m.d 0 2) (by simp) with h5445 | h5445
                                · rcases p5405_3 (m.d 1 2) (by simp) with h5446 | h5446
                                  · rcases p5405_3 (m.d 2 3) (by simp) with h5447 | h5447
                                    · linarith only [h5073, h5447, hlam]
                                    · rcases p5405_3 (m.d 2 4) (by simp) with h5449 | h5449
                                      · linarith only [h5074, h5449, hlam]
                                      · rcases p5405_3 (m.d 2 5) (by simp) with h5451 | h5451
                                        · linarith only [h5451, hlam, p5405_0]
                                        · rcases h3bigk with h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c | h5453c
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h5073, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5342_1, p5453_1]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h4553, hc23, hc35, hlam, hphi, p5342_1, p5453_1]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h7, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h4553, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h1, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h1, h4553, hc23, hc35, hlam, hphi, p5342_1, p5453_1]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h5076, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h5078, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h4, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h5073, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h5081, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h5083, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            rcases p5453_3 (m.d 0 3) (by simp) with h5469 | h5469
                                            · linarith only [h5469, hlam, p5453_0]
                                            · rcases p5453_3 (m.d 1 3) (by simp) with h5471 | h5471
                                              · linarith only [h5076, h5471, hlam]
                                              · rcases p5453_3 (m.d 2 3) (by simp) with h5473 | h5473
                                                · linarith only [h5081, h5473, hlam]
                                                · rcases p5453_3 (m.d 3 4) (by simp) with h5475 | h5475
                                                  · rcases p5453_3 (m.d 3 5) (by simp) with h5476 | h5476
                                                    · linarith only [h5341, h5476, hlam]
                                                    · linarith only [h4553, h5476, hlam]
                                                  · linarith only [h5475, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            rcases p5453_3 (m.d 0 3) (by simp) with h5480 | h5480
                                            · linarith only [h5480, h7, hlam]
                                            · linarith only [h1, h5480, hlam]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            rcases p5453_3 (m.d 0 3) (by simp) with h5483 | h5483
                                            · linarith only [h5483, h7, hlam]
                                            · linarith only [h4, h5483, hlam]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h4553, hc03, hc34, hlam, hphi, p5453_1]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            rcases p5453_3 (m.d 0 3) (by simp) with h5488 | h5488
                                            · linarith only [h5488, hlam, p5453_0]
                                            · rcases p5453_3 (m.d 1 3) (by simp) with h5490 | h5490
                                              · linarith only [h5078, h5490, hlam]
                                              · rcases p5453_3 (m.d 2 3) (by simp) with h5492 | h5492
                                                · linarith only [h5083, h5492, hlam]
                                                · rcases p5453_3 (m.d 3 4) (by simp) with h5494 | h5494
                                                  · rcases p5453_3 (m.d 3 5) (by simp) with h5495 | h5495
                                                    · rcases h5bigk with h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c | h5496c
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5072, h5073, h5078, h7, hc23, hc34, hlam, hphi, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5072, h5083, h7, hc23, hc34, hlam, hphi, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h4553, hlam, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5072, h5081, h5085, h7, hc23, hc34, hlam, hphi, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h3, hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5078, hlam, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5074, h5080, h5081, h5085, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h6, hlam, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5075, hlam, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5083, hlam, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5085, hlam, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h1, h5073, hc23, hc35, hlam, hphi, p5342_1, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5073, h5078, hc23, hc35, hlam, hphi, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5083, hc23, hc35, hlam, hphi, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5081, h5085, h5341, hc23, hc34, hlam, hphi, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5072, hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5080, hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5081, h5085, hc23, hc45, hlam, hphi, ht34, p5496_1]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [h5341, hlam, p5496_0]
                                                      · have p5496_0 := h5496c.1
                                                        have p5496_1 := h5496c.2.1
                                                        have p5496_2 := h5496c.2.2.1
                                                        have p5496_3 := h5496c.2.2.2
                                                        linarith only [hlam, p5496_0]
                                                    · linarith only [h5495, hlam, p5453_0]
                                                  · linarith only [h5494, h7, hlam]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            rcases p5453_3 (m.d 0 3) (by simp) with h5524 | h5524
                                            · linarith only [h4553, h5524, hlam]
                                            · linarith only [h1, h5524, hlam]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            rcases p5453_3 (m.d 0 3) (by simp) with h5527 | h5527
                                            · linarith only [h4553, h5527, hlam]
                                            · linarith only [h4, h5527, hlam]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [h5341, hlam, p5453_0]
                                          · have p5453_0 := h5453c.1
                                            have p5453_1 := h5453c.2.1
                                            have p5453_2 := h5453c.2.2.1
                                            have p5453_3 := h5453c.2.2.2
                                            linarith only [hlam, p5453_0]
                                  · linarith only [h5446, hlam, p5405_0]
                                · linarith only [h5445, h6, hlam]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h4, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h5073, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h5081, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h5083, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h5, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h5074, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h0, h5074, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5405_1]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h5085, hlam, p5405_1]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h6, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h5075, hlam, p5405_0]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h0, h5075, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5405_1]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [h0, h5075, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5405_1]
                              · have p5405_0 := h5405c.1
                                have p5405_1 := h5405c.2.1
                                have p5405_2 := h5405c.2.2.1
                                have p5405_3 := h5405c.2.2.2
                                linarith only [hlam, p5405_0]
                            · linarith only [h4553, h5404, hlam]
                          · linarith only [h5403, h7, hlam]
                      · linarith only [h4, h5400, hlam]
                    · linarith only [h1, h5399, hlam]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [h5072, hlam, p5342_1]
                  · have p5342_0 := h5342c.1
                    have p5342_1 := h5342c.2.1
                    have p5342_2 := h5342c.2.2.1
                    have p5342_3 := h5342c.2.2.2
                    linarith only [hlam, p5342_0]
                · linarith only [h2, h5080, h5341, h7, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5556 | h5556
          · linarith only [h5072, h5073, h5076, h5080, h5556, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5558 | h5558
            · linarith only [h1, h4553, h5073, h5558, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5560 | h5560
              · linarith only [h0, h5074, h5076, h5080, h5560, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5562 | h5562
                · rcases h0bigk with h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c | h5563c
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5, h5072, h5073, h5076, h5080, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 1) (by simp) with h5566 | h5566
                    · rcases p5563_3 (m.d 0 2) (by simp) with h5567 | h5567
                      · linarith only [h0, h5567, hlam]
                      · linarith only [h4, h5567, hlam]
                    · linarith only [h1, h5566, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5072, h5073, h5076, h5080, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 1) (by simp) with h5572 | h5572
                    · rcases p5563_3 (m.d 0 2) (by simp) with h5573 | h5573
                      · linarith only [h0, h5573, hlam]
                      · linarith only [h5573, h6, hlam]
                    · linarith only [h3, h5572, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h0, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 1) (by simp) with h5579 | h5579
                    · rcases p5563_3 (m.d 0 2) (by simp) with h5580 | h5580
                      · rcases p5563_3 (m.d 0 3) (by simp) with h5581 | h5581
                        · linarith only [h4, h5581, hlam]
                        · rcases p5563_3 (m.d 0 4) (by simp) with h5583 | h5583
                          · linarith only [h5, h5583, hlam]
                          · linarith only [h5583, h7, hlam]
                      · linarith only [h4, h5580, hlam]
                    · linarith only [h1, h5579, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5072, h5073, h5076, h5080, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 1) (by simp) with h5589 | h5589
                    · rcases p5563_3 (m.d 0 2) (by simp) with h5590 | h5590
                      · rcases p5563_3 (m.d 0 3) (by simp) with h5591 | h5591
                        · linarith only [h4, h5591, hlam]
                        · rcases p5563_3 (m.d 0 4) (by simp) with h5593 | h5593
                          · linarith only [h5, h5593, hlam]
                          · linarith only [h5072, h5593, hlam]
                      · linarith only [h5590, h6, hlam]
                    · linarith only [h3, h5589, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h1, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h7, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h4553, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h2, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 1) (by simp) with h5605 | h5605
                    · rcases p5563_3 (m.d 0 2) (by simp) with h5606 | h5606
                      · rcases p5563_3 (m.d 0 3) (by simp) with h5607 | h5607
                        · linarith only [h5607, h7, hlam]
                        · rcases p5563_3 (m.d 0 4) (by simp) with h5609 | h5609
                          · rcases p5563_3 (m.d 0 5) (by simp) with h5610 | h5610
                            · linarith only [h5072, h5610, hlam]
                            · linarith only [h4553, h5610, hlam]
                          · linarith only [h5609, h7, hlam]
                      · linarith only [h4, h5606, hlam]
                    · linarith only [h1, h5605, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5072, h5073, h5076, h5080, h7, hc23, hc34, hlam, hphi, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h3, hlam, p5563_0]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h6, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    rcases p5563_3 (m.d 0 1) (by simp) with h5620 | h5620
                    · rcases p5563_3 (m.d 0 2) (by simp) with h5621 | h5621
                      · rcases p5563_3 (m.d 0 3) (by simp) with h5622 | h5622
                        · linarith only [h4553, h5622, hlam]
                        · rcases p5563_3 (m.d 0 4) (by simp) with h5624 | h5624
                          · rcases p5563_3 (m.d 0 5) (by simp) with h5625 | h5625
                            · rcases h2bigk with h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c | h5626c
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                rcases p5626_3 (m.d 0 2) (by simp) with h5628 | h5628
                                · rcases p5626_3 (m.d 1 2) (by simp) with h5629 | h5629
                                  · linarith only [h0, h5629, hlam]
                                  · rcases p5626_3 (m.d 2 3) (by simp) with h5631 | h5631
                                    · linarith only [h4, h5631, hlam]
                                    · rcases p5626_3 (m.d 2 4) (by simp) with h5633 | h5633
                                      · linarith only [h5, h5633, hlam]
                                      · rcases p5626_3 (m.d 2 5) (by simp) with h5635 | h5635
                                        · linarith only [h5635, h6, hlam]
                                        · rcases h3bigk with h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5073, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1, p5637_1]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h4553, hc23, hc35, hlam, hphi, p5563_1, p5637_1]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h7, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h4553, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h1, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5076, h5080, hc23, hc45, hlam, hphi, ht34, p5637_1]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5076, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5078, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h4, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5073, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5556, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5558, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            rcases p5637_3 (m.d 0 3) (by simp) with h5653 | h5653
                                            · linarith only [h5653, hlam, p5637_0]
                                            · rcases p5637_3 (m.d 1 3) (by simp) with h5655 | h5655
                                              · linarith only [h5076, h5655, hlam]
                                              · rcases p5637_3 (m.d 2 3) (by simp) with h5657 | h5657
                                                · linarith only [h5556, h5657, hlam]
                                                · rcases p5637_3 (m.d 3 4) (by simp) with h5659 | h5659
                                                  · rcases p5637_3 (m.d 3 5) (by simp) with h5660 | h5660
                                                    · linarith only [h5562, h5660, hlam]
                                                    · linarith only [h4553, h5660, hlam]
                                                  · linarith only [h5659, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            rcases p5637_3 (m.d 0 3) (by simp) with h5664 | h5664
                                            · linarith only [h5664, h7, hlam]
                                            · linarith only [h1, h5664, hlam]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            rcases p5637_3 (m.d 0 3) (by simp) with h5667 | h5667
                                            · linarith only [h5667, h7, hlam]
                                            · linarith only [h4, h5667, hlam]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h4553, hc03, hc34, hlam, hphi, p5637_1]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            rcases p5637_3 (m.d 0 3) (by simp) with h5672 | h5672
                                            · linarith only [h5672, hlam, p5637_0]
                                            · rcases p5637_3 (m.d 1 3) (by simp) with h5674 | h5674
                                              · linarith only [h5078, h5674, hlam]
                                              · rcases p5637_3 (m.d 2 3) (by simp) with h5676 | h5676
                                                · linarith only [h5558, h5676, hlam]
                                                · rcases p5637_3 (m.d 3 4) (by simp) with h5678 | h5678
                                                  · rcases p5637_3 (m.d 3 5) (by simp) with h5679 | h5679
                                                    · rcases h5bigk with h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c | h5680c
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [hlam, p5680_0]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5072, h5073, h5078, h7, hc23, hc34, hlam, hphi, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5072, h5556, h5560, h7, hc23, hc34, hlam, hphi, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h4553, hlam, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5072, h5073, h5076, h5080, h7, hc23, hc34, hlam, hphi, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h3, hlam, p5680_0]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [hlam, p5680_0]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h3, h5560, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5078, hlam, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5080, hlam, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h6, hlam, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5075, hlam, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [hlam, p5680_0]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5558, hlam, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5560, hlam, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h1, h5073, hc23, hc35, hlam, hphi, p5563_1, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5073, h5078, hc23, hc35, hlam, hphi, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5556, h5560, hc23, hc35, hlam, hphi, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [hlam, p5680_0]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5073, h5076, h5080, h5562, hc23, hc34, hlam, hphi, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5072, hlam, p5680_0]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5073, h5076, h5080, hc23, hc45, hlam, hphi, ht34, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5072, h5556, h5560, h7, hc23, hc34, hlam, hphi, p5680_1]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [h5562, hlam, p5680_0]
                                                      · have p5680_0 := h5680c.1
                                                        have p5680_1 := h5680c.2.1
                                                        have p5680_2 := h5680c.2.2.1
                                                        have p5680_3 := h5680c.2.2.2
                                                        linarith only [hlam, p5680_0]
                                                    · linarith only [h5679, hlam, p5637_0]
                                                  · linarith only [h5678, h7, hlam]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            rcases p5637_3 (m.d 0 3) (by simp) with h5708 | h5708
                                            · linarith only [h4553, h5708, hlam]
                                            · linarith only [h1, h5708, hlam]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            rcases p5637_3 (m.d 0 3) (by simp) with h5711 | h5711
                                            · linarith only [h4553, h5711, hlam]
                                            · linarith only [h4, h5711, hlam]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [h5562, hlam, p5637_0]
                                          · have p5637_0 := h5637c.1
                                            have p5637_1 := h5637c.2.1
                                            have p5637_2 := h5637c.2.2.1
                                            have p5637_3 := h5637c.2.2.2
                                            linarith only [hlam, p5637_0]
                                · linarith only [h0, h5628, hlam]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                rcases p5626_3 (m.d 0 2) (by simp) with h5717 | h5717
                                · rcases p5626_3 (m.d 1 2) (by simp) with h5718 | h5718
                                  · linarith only [h0, h5718, hlam]
                                  · linarith only [h5073, h5718, hlam]
                                · linarith only [h5717, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                rcases p5626_3 (m.d 0 2) (by simp) with h5722 | h5722
                                · rcases p5626_3 (m.d 1 2) (by simp) with h5723 | h5723
                                  · linarith only [h0, h5723, hlam]
                                  · linarith only [h5074, h5723, hlam]
                                · linarith only [h5722, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                rcases p5626_3 (m.d 0 2) (by simp) with h5727 | h5727
                                · rcases p5626_3 (m.d 1 2) (by simp) with h5728 | h5728
                                  · linarith only [h0, h5728, hlam]
                                  · linarith only [h5075, h5728, hlam]
                                · linarith only [h5727, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h0, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                rcases p5626_3 (m.d 0 2) (by simp) with h5734 | h5734
                                · rcases p5626_3 (m.d 1 2) (by simp) with h5735 | h5735
                                  · rcases p5626_3 (m.d 2 3) (by simp) with h5736 | h5736
                                    · linarith only [h5736, hlam, p5626_0]
                                    · rcases p5626_3 (m.d 2 4) (by simp) with h5738 | h5738
                                      · linarith only [h5074, h5738, hlam]
                                      · linarith only [h5556, h5738, hlam]
                                  · linarith only [h5735, hlam, p5626_0]
                                · linarith only [h4, h5734, hlam]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                rcases p5626_3 (m.d 0 2) (by simp) with h5743 | h5743
                                · rcases p5626_3 (m.d 1 2) (by simp) with h5744 | h5744
                                  · rcases p5626_3 (m.d 2 3) (by simp) with h5745 | h5745
                                    · linarith only [h5073, h5745, hlam]
                                    · rcases p5626_3 (m.d 2 4) (by simp) with h5747 | h5747
                                      · linarith only [h5747, hlam, p5626_0]
                                      · rcases p5626_3 (m.d 2 5) (by simp) with h5749 | h5749
                                        · linarith only [h5075, h5749, hlam]
                                        · linarith only [h5560, h5749, hlam]
                                  · linarith only [h5744, hlam, p5626_0]
                                · linarith only [h5, h5743, hlam]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                rcases p5626_3 (m.d 0 2) (by simp) with h5754 | h5754
                                · rcases p5626_3 (m.d 1 2) (by simp) with h5755 | h5755
                                  · rcases p5626_3 (m.d 2 3) (by simp) with h5756 | h5756
                                    · linarith only [h5073, h5756, hlam]
                                    · rcases p5626_3 (m.d 2 4) (by simp) with h5758 | h5758
                                      · linarith only [h5074, h5758, hlam]
                                      · rcases p5626_3 (m.d 2 5) (by simp) with h5760 | h5760
                                        · linarith only [h5760, hlam, p5626_0]
                                        · rcases h3bigk with h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c | h5762c
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h5073, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1, p5762_1]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1, p5762_1]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h7, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h4553, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h1, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h1, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5563_1, p5762_1]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h5076, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h5078, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h4, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h5073, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h5556, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h5558, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            rcases p5762_3 (m.d 0 3) (by simp) with h5778 | h5778
                                            · linarith only [h5778, hlam, p5762_0]
                                            · rcases p5762_3 (m.d 1 3) (by simp) with h5780 | h5780
                                              · linarith only [h5076, h5780, hlam]
                                              · rcases p5762_3 (m.d 2 3) (by simp) with h5782 | h5782
                                                · linarith only [h5556, h5782, hlam]
                                                · rcases p5762_3 (m.d 3 4) (by simp) with h5784 | h5784
                                                  · rcases p5762_3 (m.d 3 5) (by simp) with h5785 | h5785
                                                    · linarith only [h5562, h5785, hlam]
                                                    · linarith only [h4553, h5785, hlam]
                                                  · linarith only [h5784, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            rcases p5762_3 (m.d 0 3) (by simp) with h5789 | h5789
                                            · linarith only [h5789, h7, hlam]
                                            · linarith only [h1, h5789, hlam]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            rcases p5762_3 (m.d 0 3) (by simp) with h5792 | h5792
                                            · linarith only [h5792, h7, hlam]
                                            · linarith only [h4, h5792, hlam]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h4553, hc03, hc34, hlam, hphi, p5563_1, p5762_1]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            rcases p5762_3 (m.d 0 3) (by simp) with h5797 | h5797
                                            · linarith only [h5797, hlam, p5762_0]
                                            · rcases p5762_3 (m.d 1 3) (by simp) with h5799 | h5799
                                              · linarith only [h5078, h5799, hlam]
                                              · rcases p5762_3 (m.d 2 3) (by simp) with h5801 | h5801
                                                · linarith only [h5558, h5801, hlam]
                                                · rcases p5762_3 (m.d 3 4) (by simp) with h5803 | h5803
                                                  · rcases p5762_3 (m.d 3 5) (by simp) with h5804 | h5804
                                                    · rcases h5bigk with h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c | h5805c
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [hlam, p5805_0]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h4553, h5073, h5076, h5080, hc23, hc35, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h4553, h5556, h5560, hc23, hc35, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h4553, hlam, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5072, h5073, h5076, h5080, h7, hc23, hc34, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h3, hlam, p5805_0]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [hlam, p5805_0]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h3, h5556, h5560, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5078, hlam, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5080, hlam, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h6, hlam, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5075, hlam, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [hlam, p5805_0]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5558, hlam, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5560, hlam, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5556, h5560, h6, hc23, hc35, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5075, h5556, h5560, hc23, hc35, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5556, h5560, hc23, hc35, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [hlam, p5805_0]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5073, h5076, h5080, h5562, hc23, hc34, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5072, hlam, p5805_0]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5075, h5556, h5560, hc23, hc45, hlam, hphi, ht34, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5072, h5556, h5560, h7, hc23, hc34, hlam, hphi, p5805_1]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [h5562, hlam, p5805_0]
                                                      · have p5805_0 := h5805c.1
                                                        have p5805_1 := h5805c.2.1
                                                        have p5805_2 := h5805c.2.2.1
                                                        have p5805_3 := h5805c.2.2.2
                                                        linarith only [hlam, p5805_0]
                                                    · linarith only [h5804, hlam, p5762_0]
                                                  · linarith only [h5803, h7, hlam]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            rcases p5762_3 (m.d 0 3) (by simp) with h5833 | h5833
                                            · linarith only [h4553, h5833, hlam]
                                            · linarith only [h1, h5833, hlam]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            rcases p5762_3 (m.d 0 3) (by simp) with h5836 | h5836
                                            · linarith only [h4553, h5836, hlam]
                                            · linarith only [h4, h5836, hlam]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [h5562, hlam, p5762_0]
                                          · have p5762_0 := h5762c.1
                                            have p5762_1 := h5762c.2.1
                                            have p5762_2 := h5762c.2.2.1
                                            have p5762_3 := h5762c.2.2.2
                                            linarith only [hlam, p5762_0]
                                  · linarith only [h5755, hlam, p5626_0]
                                · linarith only [h5754, h6, hlam]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h4, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h5073, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h5556, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h5558, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h5, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h5074, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h0, h5074, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5626_1]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h5560, hlam, p5626_1]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h6, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h5075, hlam, p5626_0]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h0, h5075, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5626_1]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [h0, h5075, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p5626_1]
                              · have p5626_0 := h5626c.1
                                have p5626_1 := h5626c.2.1
                                have p5626_2 := h5626c.2.2.1
                                have p5626_3 := h5626c.2.2.2
                                linarith only [hlam, p5626_0]
                            · linarith only [h4553, h5625, hlam]
                          · linarith only [h5624, h7, hlam]
                      · linarith only [h4, h5621, hlam]
                    · linarith only [h1, h5620, hlam]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [h5072, hlam, p5563_1]
                  · have p5563_0 := h5563c.1
                    have p5563_1 := h5563c.2.1
                    have p5563_2 := h5563c.2.2.1
                    have p5563_3 := h5563c.2.2.2
                    linarith only [hlam, p5563_0]
                · linarith only [h5072, h5562, h7, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5865 | h5865
    · linarith only [h1, h5865, h7, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5867 | h5867
      · linarith only [h1, h4553, h5867, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5869 | h5869
        · linarith only [h5074, h5075, h5869, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5871 | h5871
          · linarith only [h5072, h5073, h5865, h5869, h5871, h7, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5873 | h5873
            · linarith only [h1, h4553, h5073, h5075, h5873, h6, h7, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5875 | h5875
              · linarith only [h5074, h5075, h5865, h5869, h5875, h6, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h5072, h5073, h5075, h5875, h7, hc23, hc34, hlam, hphi]

end R2N4
