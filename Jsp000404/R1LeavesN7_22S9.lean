import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_22S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4344 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4345 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h4346 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 2 3 5 (by decide) (by decide) with h5120 | h5120
  · rcases m.htr 2 4 5 (by decide) (by decide) with h5121 | h5121
    · rcases m.htr 3 4 5 (by decide) (by decide) with h5122 | h5122
      · rcases h0bigk with h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h0, hlam, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h3609, hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4113, hlam, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          rcases p5123_3 (m.d 0 1) (by simp) with h5128 | h5128
          · rcases p5123_3 (m.d 0 2) (by simp) with h5129 | h5129
            · rcases p5123_3 (m.d 0 3) (by simp) with h5130 | h5130
              · rcases p5123_3 (m.d 0 4) (by simp) with h5131 | h5131
                · rcases p5123_3 (m.d 0 5) (by simp) with h5132 | h5132
                  · linarith only [h4333, h5132, hlam]
                  · rcases h0emin with h5134 | h5134 | h5134 | h5134 | h5134
                    · linarith only [h4113, h4340, h4343, h5134, hc12, hlam, ht01]
                    · rcases h2bigk with h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h0, hlam, p5136_1]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        rcases p5136_3 (m.d 0 2) (by simp) with h5139 | h5139
                        · rcases p5136_3 (m.d 1 2) (by simp) with h5140 | h5140
                          · rcases p5136_3 (m.d 2 3) (by simp) with h5141 | h5141
                            · linarith only [h5141, hlam, p5136_0]
                            · rcases p5136_3 (m.d 2 4) (by simp) with h5143 | h5143
                              · linarith only [h4335, h5143, hlam]
                              · linarith only [h4346, h5143, hlam]
                          · linarith only [h4340, h5140, hlam]
                        · linarith only [h5139, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        rcases p5136_3 (m.d 0 2) (by simp) with h5148 | h5148
                        · rcases p5136_3 (m.d 1 2) (by simp) with h5149 | h5149
                          · rcases p5136_3 (m.d 2 3) (by simp) with h5150 | h5150
                            · linarith only [h4334, h5150, hlam]
                            · rcases p5136_3 (m.d 2 4) (by simp) with h5152 | h5152
                              · linarith only [h5152, hlam, p5136_0]
                              · rcases p5136_3 (m.d 2 5) (by simp) with h5154 | h5154
                                · linarith only [h4336, h5154, hlam]
                                · rcases h3bigk with h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h3609, hlam, p5156_1]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    rcases p5156_3 (m.d 0 3) (by simp) with h5159 | h5159
                                    · rcases p5156_3 (m.d 1 3) (by simp) with h5160 | h5160
                                      · rcases p5156_3 (m.d 2 3) (by simp) with h5161 | h5161
                                        · linarith only [h4334, h5161, hlam]
                                        · rcases p5156_3 (m.d 3 4) (by simp) with h5163 | h5163
                                          · linarith only [h4337, h5163, hlam]
                                          · linarith only [h4346, h5163, hlam]
                                      · linarith only [h4340, h5160, hlam]
                                    · linarith only [h4334, h5159, hlam]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h0, h4334, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5156_1]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4337, h4346, h5120, hlam, p5156_2]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h3609, h4340, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5123_1, p5156_1]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    rcases p5156_3 (m.d 0 3) (by simp) with h5172 | h5172
                                    · linarith only [h3609, h5172, hlam]
                                    · linarith only [h4334, h5172, hlam]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5156_1]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h3609, h4333, h4342, h5120, hlam, p5123_1, p5156_2]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4334, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4340, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4346, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4337, h4346, h5122, hc03, hc45, hlam, hphi, ht0b, ht5b, p5156_1]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4337, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4343, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h0, h4334, h4337, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5156_1]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    rcases p5156_3 (m.d 0 3) (by simp) with h5186 | h5186
                                    · rcases p5156_3 (m.d 1 3) (by simp) with h5187 | h5187
                                      · rcases p5156_3 (m.d 2 3) (by simp) with h5188 | h5188
                                        · linarith only [h4346, h5188, hlam]
                                        · linarith only [h5120, h5188, hlam]
                                      · linarith only [h4344, h5187, hlam]
                                    · linarith only [h4338, h5186, hlam]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4338, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h4344, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h5120, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [h5122, hlam, p5156_0]
                                  · have p5156_0 := h5156c.1
                                    have p5156_1 := h5156c.2.1
                                    have p5156_2 := h5156c.2.2.1
                                    have p5156_3 := h5156c.2.2.2
                                    linarith only [hlam, p5156_0]
                          · linarith only [h4341, h5149, hlam]
                        · linarith only [h5148, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        rcases p5136_3 (m.d 0 2) (by simp) with h5200 | h5200
                        · rcases p5136_3 (m.d 1 2) (by simp) with h5201 | h5201
                          · rcases p5136_3 (m.d 2 3) (by simp) with h5202 | h5202
                            · linarith only [h4334, h5202, hlam]
                            · linarith only [h5120, h5202, hlam]
                          · linarith only [h4342, h5201, hlam]
                        · linarith only [h5200, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4334, h4337, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5136_1]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        rcases p5136_3 (m.d 0 2) (by simp) with h5209 | h5209
                        · linarith only [h0, h5209, hlam]
                        · linarith only [h4334, h5209, hlam]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        rcases p5136_3 (m.d 0 2) (by simp) with h5212 | h5212
                        · linarith only [h0, h5212, hlam]
                        · linarith only [h4335, h5212, hlam]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h0, h4333, h4342, hlam, p5123_1, p5136_2]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4334, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4340, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4346, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4334, h4337, h4346, hc02, hc25, hlam, hphi, ht0b, ht5b, p5136_1]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4335, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4341, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h0, h4335, h5120, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5136_1]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        rcases p5136_3 (m.d 0 2) (by simp) with h5225 | h5225
                        · rcases p5136_3 (m.d 1 2) (by simp) with h5226 | h5226
                          · rcases p5136_3 (m.d 2 3) (by simp) with h5227 | h5227
                            · linarith only [h4346, h5227, hlam]
                            · linarith only [h5120, h5227, hlam]
                          · linarith only [h4342, h5226, hlam]
                        · linarith only [h4336, h5225, hlam]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4336, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h4342, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h5120, hlam, p5136_1]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [h5121, hlam, p5136_0]
                      · have p5136_0 := h5136c.1
                        have p5136_1 := h5136c.2.1
                        have p5136_2 := h5136c.2.2.1
                        have p5136_3 := h5136c.2.2.2
                        linarith only [hlam, p5136_0]
                    · rcases h2bigk with h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c | h5237c
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h0, hlam, p5237_1]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        rcases p5237_3 (m.d 0 2) (by simp) with h5240 | h5240
                        · rcases p5237_3 (m.d 1 2) (by simp) with h5241 | h5241
                          · rcases p5237_3 (m.d 2 3) (by simp) with h5242 | h5242
                            · linarith only [h5242, hlam, p5237_0]
                            · rcases p5237_3 (m.d 2 4) (by simp) with h5244 | h5244
                              · linarith only [h4335, h5244, hlam]
                              · linarith only [h4346, h5244, hlam]
                          · linarith only [h4340, h5241, hlam]
                        · linarith only [h5240, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        rcases p5237_3 (m.d 0 2) (by simp) with h5249 | h5249
                        · rcases p5237_3 (m.d 1 2) (by simp) with h5250 | h5250
                          · rcases p5237_3 (m.d 2 3) (by simp) with h5251 | h5251
                            · linarith only [h4334, h5251, hlam]
                            · rcases p5237_3 (m.d 2 4) (by simp) with h5253 | h5253
                              · linarith only [h5253, hlam, p5237_0]
                              · rcases p5237_3 (m.d 2 5) (by simp) with h5255 | h5255
                                · linarith only [h4336, h5255, hlam]
                                · rcases h3bigk with h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c | h5257c
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h3609, hlam, p5257_1]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    rcases p5257_3 (m.d 0 3) (by simp) with h5260 | h5260
                                    · rcases p5257_3 (m.d 1 3) (by simp) with h5261 | h5261
                                      · rcases p5257_3 (m.d 2 3) (by simp) with h5262 | h5262
                                        · linarith only [h4334, h5262, hlam]
                                        · rcases p5257_3 (m.d 3 4) (by simp) with h5264 | h5264
                                          · linarith only [h4337, h5264, hlam]
                                          · linarith only [h4346, h5264, hlam]
                                      · linarith only [h4340, h5261, hlam]
                                    · linarith only [h4334, h5260, hlam]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h0, h4334, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5257_1]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4337, h4346, h5120, hlam, p5257_2]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h5134, hc13, hlam, ht01, p5257_1]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    rcases p5257_3 (m.d 0 3) (by simp) with h5273 | h5273
                                    · linarith only [h3609, h5273, hlam]
                                    · linarith only [h4334, h5273, hlam]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5257_1]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h3609, h4333, h4342, h5120, hlam, p5123_1, p5257_2]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4334, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4340, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4346, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4337, h4346, h5122, hc03, hc45, hlam, hphi, ht0b, ht5b, p5257_1]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4337, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4343, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h0, h4334, h4337, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5257_1]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    rcases p5257_3 (m.d 0 3) (by simp) with h5287 | h5287
                                    · rcases p5257_3 (m.d 1 3) (by simp) with h5288 | h5288
                                      · rcases p5257_3 (m.d 2 3) (by simp) with h5289 | h5289
                                        · linarith only [h4346, h5289, hlam]
                                        · linarith only [h5120, h5289, hlam]
                                      · linarith only [h4344, h5288, hlam]
                                    · linarith only [h4338, h5287, hlam]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4338, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h4344, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h5120, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [h5122, hlam, p5257_0]
                                  · have p5257_0 := h5257c.1
                                    have p5257_1 := h5257c.2.1
                                    have p5257_2 := h5257c.2.2.1
                                    have p5257_3 := h5257c.2.2.2
                                    linarith only [hlam, p5257_0]
                          · linarith only [h4341, h5250, hlam]
                        · linarith only [h5249, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        rcases p5237_3 (m.d 0 2) (by simp) with h5301 | h5301
                        · rcases p5237_3 (m.d 1 2) (by simp) with h5302 | h5302
                          · rcases p5237_3 (m.d 2 3) (by simp) with h5303 | h5303
                            · linarith only [h4334, h5303, hlam]
                            · linarith only [h5120, h5303, hlam]
                          · linarith only [h4342, h5302, hlam]
                        · linarith only [h5301, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4334, h4337, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5237_1]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        rcases p5237_3 (m.d 0 2) (by simp) with h5310 | h5310
                        · linarith only [h0, h5310, hlam]
                        · linarith only [h4334, h5310, hlam]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        rcases p5237_3 (m.d 0 2) (by simp) with h5313 | h5313
                        · linarith only [h0, h5313, hlam]
                        · linarith only [h4335, h5313, hlam]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h0, h4333, h4342, hlam, p5123_1, p5237_2]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4334, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4340, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4346, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4334, h4337, h4346, hc02, hc25, hlam, hphi, ht0b, ht5b, p5237_1]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4335, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4341, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h0, h4335, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5237_1]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        rcases p5237_3 (m.d 0 2) (by simp) with h5326 | h5326
                        · rcases p5237_3 (m.d 1 2) (by simp) with h5327 | h5327
                          · rcases p5237_3 (m.d 2 3) (by simp) with h5328 | h5328
                            · linarith only [h4346, h5328, hlam]
                            · linarith only [h5120, h5328, hlam]
                          · linarith only [h4342, h5327, hlam]
                        · linarith only [h4336, h5326, hlam]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4336, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h4342, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h5120, hlam, p5237_1]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [h5121, hlam, p5237_0]
                      · have p5237_0 := h5237c.1
                        have p5237_1 := h5237c.2.1
                        have p5237_2 := h5237c.2.2.1
                        have p5237_3 := h5237c.2.2.2
                        linarith only [hlam, p5237_0]
                    · rcases h2bigk with h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c | h5338c
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h0, hlam, p5338_1]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        rcases p5338_3 (m.d 0 2) (by simp) with h5341 | h5341
                        · rcases p5338_3 (m.d 1 2) (by simp) with h5342 | h5342
                          · rcases p5338_3 (m.d 2 3) (by simp) with h5343 | h5343
                            · linarith only [h5343, hlam, p5338_0]
                            · rcases p5338_3 (m.d 2 4) (by simp) with h5345 | h5345
                              · linarith only [h4335, h5345, hlam]
                              · linarith only [h4346, h5345, hlam]
                          · linarith only [h4340, h5342, hlam]
                        · linarith only [h5341, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        rcases p5338_3 (m.d 0 2) (by simp) with h5350 | h5350
                        · rcases p5338_3 (m.d 1 2) (by simp) with h5351 | h5351
                          · rcases p5338_3 (m.d 2 3) (by simp) with h5352 | h5352
                            · linarith only [h4334, h5352, hlam]
                            · rcases p5338_3 (m.d 2 4) (by simp) with h5354 | h5354
                              · linarith only [h5354, hlam, p5338_0]
                              · rcases p5338_3 (m.d 2 5) (by simp) with h5356 | h5356
                                · linarith only [h4336, h5356, hlam]
                                · rcases h3bigk with h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c | h5358c
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h3609, hlam, p5358_1]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    rcases p5358_3 (m.d 0 3) (by simp) with h5361 | h5361
                                    · rcases p5358_3 (m.d 1 3) (by simp) with h5362 | h5362
                                      · rcases p5358_3 (m.d 2 3) (by simp) with h5363 | h5363
                                        · linarith only [h4334, h5363, hlam]
                                        · rcases p5358_3 (m.d 3 4) (by simp) with h5365 | h5365
                                          · linarith only [h4337, h5365, hlam]
                                          · linarith only [h4346, h5365, hlam]
                                      · linarith only [h4340, h5362, hlam]
                                    · linarith only [h4334, h5361, hlam]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h0, h4334, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5358_1]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4337, h4346, h5120, hlam, p5358_2]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h3609, h4333, h4342, h5120, h5122, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p5123_1, p5358_1]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    rcases p5358_3 (m.d 0 3) (by simp) with h5374 | h5374
                                    · linarith only [h3609, h5374, hlam]
                                    · linarith only [h4334, h5374, hlam]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5358_1]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h3609, h4333, h4342, h5120, hlam, p5123_1, p5358_2]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4334, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4340, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4346, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4337, h4346, h5122, hc03, hc45, hlam, hphi, ht0b, ht5b, p5358_1]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4337, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4343, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h0, h4334, h4337, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5358_1]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    rcases p5358_3 (m.d 0 3) (by simp) with h5388 | h5388
                                    · rcases p5358_3 (m.d 1 3) (by simp) with h5389 | h5389
                                      · rcases p5358_3 (m.d 2 3) (by simp) with h5390 | h5390
                                        · linarith only [h4346, h5390, hlam]
                                        · linarith only [h5120, h5390, hlam]
                                      · linarith only [h4344, h5389, hlam]
                                    · linarith only [h4338, h5388, hlam]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4338, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h4344, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h5120, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [h5122, hlam, p5358_0]
                                  · have p5358_0 := h5358c.1
                                    have p5358_1 := h5358c.2.1
                                    have p5358_2 := h5358c.2.2.1
                                    have p5358_3 := h5358c.2.2.2
                                    linarith only [hlam, p5358_0]
                          · linarith only [h4341, h5351, hlam]
                        · linarith only [h5350, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        rcases p5338_3 (m.d 0 2) (by simp) with h5402 | h5402
                        · rcases p5338_3 (m.d 1 2) (by simp) with h5403 | h5403
                          · rcases p5338_3 (m.d 2 3) (by simp) with h5404 | h5404
                            · linarith only [h4334, h5404, hlam]
                            · linarith only [h5120, h5404, hlam]
                          · linarith only [h4342, h5403, hlam]
                        · linarith only [h5402, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4334, h4337, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5338_1]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        rcases p5338_3 (m.d 0 2) (by simp) with h5411 | h5411
                        · linarith only [h0, h5411, hlam]
                        · linarith only [h4334, h5411, hlam]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        rcases p5338_3 (m.d 0 2) (by simp) with h5414 | h5414
                        · linarith only [h0, h5414, hlam]
                        · linarith only [h4335, h5414, hlam]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h0, h4333, h4342, hlam, p5123_1, p5338_2]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4334, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4340, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4346, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4334, h4337, h4346, hc02, hc25, hlam, hphi, ht0b, ht5b, p5338_1]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4335, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4341, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h0, h4335, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5338_1]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        rcases p5338_3 (m.d 0 2) (by simp) with h5427 | h5427
                        · rcases p5338_3 (m.d 1 2) (by simp) with h5428 | h5428
                          · rcases p5338_3 (m.d 2 3) (by simp) with h5429 | h5429
                            · linarith only [h4346, h5429, hlam]
                            · linarith only [h5120, h5429, hlam]
                          · linarith only [h4342, h5428, hlam]
                        · linarith only [h4336, h5427, hlam]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4336, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h4342, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h5120, hlam, p5338_1]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [h5121, hlam, p5338_0]
                      · have p5338_0 := h5338c.1
                        have p5338_1 := h5338c.2.1
                        have p5338_2 := h5338c.2.2.1
                        have p5338_3 := h5338c.2.2.2
                        linarith only [hlam, p5338_0]
                    · linarith only [h5134, hc01, hlam, p5123_1]
                · linarith only [h4339, h5131, hlam]
              · linarith only [h4338, h5130, hlam]
            · linarith only [h4336, h5129, hlam]
          · linarith only [h4333, h5128, hlam]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          rcases p5123_3 (m.d 0 1) (by simp) with h5444 | h5444
          · linarith only [h0, h5444, hlam]
          · rcases p5123_3 (m.d 0 2) (by simp) with h5446 | h5446
            · rcases p5123_3 (m.d 0 3) (by simp) with h5447 | h5447
              · linarith only [h4334, h5447, hlam]
              · linarith only [h3609, h5447, hlam]
            · linarith only [h0, h5446, hlam]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h0, h4337, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h0, h4337, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          rcases p5123_3 (m.d 0 1) (by simp) with h5454 | h5454
          · linarith only [h0, h5454, hlam]
          · linarith only [h4333, h5454, hlam]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          rcases p5123_3 (m.d 0 1) (by simp) with h5457 | h5457
          · linarith only [h3609, h5457, hlam]
          · rcases p5123_3 (m.d 0 2) (by simp) with h5459 | h5459
            · rcases p5123_3 (m.d 0 3) (by simp) with h5460 | h5460
              · rcases p5123_3 (m.d 0 4) (by simp) with h5461 | h5461
                · linarith only [h4337, h5461, hlam]
                · linarith only [h4113, h5461, hlam]
              · linarith only [h3609, h5460, hlam]
            · linarith only [h0, h5459, hlam]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4334, hlam, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4337, h4346, h5120, h5122, hc03, hc45, hlam, hphi, ht0b, ht5b, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          rcases p5123_3 (m.d 0 1) (by simp) with h5469 | h5469
          · linarith only [h3609, h5469, hlam]
          · linarith only [h4333, h5469, hlam]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          rcases p5123_3 (m.d 0 1) (by simp) with h5472 | h5472
          · linarith only [h4113, h5472, hlam]
          · rcases p5123_3 (m.d 0 2) (by simp) with h5474 | h5474
            · rcases p5123_3 (m.d 0 3) (by simp) with h5475 | h5475
              · rcases p5123_3 (m.d 0 4) (by simp) with h5476 | h5476
                · rcases p5123_3 (m.d 0 5) (by simp) with h5477 | h5477
                  · linarith only [h4339, h5477, hlam]
                  · rcases h0emin with h5479 | h5479 | h5479 | h5479 | h5479
                    · linarith only [h5479, hc04, hlam, p5123_1]
                    · rcases h2bigk with h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c | h5481c
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h0, hlam, p5481_1]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        rcases p5481_3 (m.d 0 2) (by simp) with h5484 | h5484
                        · rcases p5481_3 (m.d 1 2) (by simp) with h5485 | h5485
                          · rcases p5481_3 (m.d 2 3) (by simp) with h5486 | h5486
                            · linarith only [h5486, hlam, p5481_0]
                            · rcases p5481_3 (m.d 2 4) (by simp) with h5488 | h5488
                              · linarith only [h4335, h5488, hlam]
                              · linarith only [h4346, h5488, hlam]
                          · linarith only [h4340, h5485, hlam]
                        · linarith only [h5484, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        rcases p5481_3 (m.d 0 2) (by simp) with h5493 | h5493
                        · rcases p5481_3 (m.d 1 2) (by simp) with h5494 | h5494
                          · rcases p5481_3 (m.d 2 3) (by simp) with h5495 | h5495
                            · linarith only [h4334, h5495, hlam]
                            · rcases p5481_3 (m.d 2 4) (by simp) with h5497 | h5497
                              · linarith only [h5497, hlam, p5481_0]
                              · rcases p5481_3 (m.d 2 5) (by simp) with h5499 | h5499
                                · linarith only [h4336, h5499, hlam]
                                · rcases h3bigk with h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c | h5501c
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h3609, hlam, p5501_1]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    rcases p5501_3 (m.d 0 3) (by simp) with h5504 | h5504
                                    · rcases p5501_3 (m.d 1 3) (by simp) with h5505 | h5505
                                      · rcases p5501_3 (m.d 2 3) (by simp) with h5506 | h5506
                                        · linarith only [h4334, h5506, hlam]
                                        · rcases p5501_3 (m.d 3 4) (by simp) with h5508 | h5508
                                          · linarith only [h4337, h5508, hlam]
                                          · linarith only [h4346, h5508, hlam]
                                      · linarith only [h4340, h5505, hlam]
                                    · linarith only [h4334, h5504, hlam]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h3609, h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5501_1]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4337, h4346, h5120, hlam, p5501_2]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4337, h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5501_1]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    rcases p5501_3 (m.d 0 3) (by simp) with h5517 | h5517
                                    · linarith only [h3609, h5517, hlam]
                                    · linarith only [h4334, h5517, hlam]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5501_1]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4113, h4333, h4342, h4343, h5120, hlam, p5123_1, p5501_2]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4334, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4340, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4346, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4337, h4346, h5122, hc03, hc45, hlam, hphi, ht0b, ht5b, p5501_1]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4337, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4343, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h0, h4334, h4337, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5501_1]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    rcases p5501_3 (m.d 0 3) (by simp) with h5531 | h5531
                                    · rcases p5501_3 (m.d 1 3) (by simp) with h5532 | h5532
                                      · rcases p5501_3 (m.d 2 3) (by simp) with h5533 | h5533
                                        · linarith only [h4346, h5533, hlam]
                                        · linarith only [h5120, h5533, hlam]
                                      · linarith only [h4344, h5532, hlam]
                                    · linarith only [h4338, h5531, hlam]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4338, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h4344, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h5120, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [h5122, hlam, p5501_0]
                                  · have p5501_0 := h5501c.1
                                    have p5501_1 := h5501c.2.1
                                    have p5501_2 := h5501c.2.2.1
                                    have p5501_3 := h5501c.2.2.2
                                    linarith only [hlam, p5501_0]
                          · linarith only [h4341, h5494, hlam]
                        · linarith only [h5493, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4333, h4335, h4342, hlam, p5123_1, p5481_2]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h5479, hc12, hlam, ht01, p5481_1]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        rcases p5481_3 (m.d 0 2) (by simp) with h5548 | h5548
                        · linarith only [h0, h5548, hlam]
                        · linarith only [h4334, h5548, hlam]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        rcases p5481_3 (m.d 0 2) (by simp) with h5551 | h5551
                        · linarith only [h0, h5551, hlam]
                        · linarith only [h4335, h5551, hlam]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h0, h4333, h4334, h4337, h4342, hlam, p5123_1, p5481_2]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4334, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4340, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4346, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4334, h4337, h4346, h5120, h5122, hc02, hc45, hlam, hphi, ht0b, ht5b, p5481_1]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4335, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4341, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h0, h4334, h4337, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5481_1]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        rcases p5481_3 (m.d 0 2) (by simp) with h5564 | h5564
                        · rcases p5481_3 (m.d 1 2) (by simp) with h5565 | h5565
                          · rcases p5481_3 (m.d 2 3) (by simp) with h5566 | h5566
                            · linarith only [h4346, h5566, hlam]
                            · linarith only [h5120, h5566, hlam]
                          · linarith only [h4342, h5565, hlam]
                        · linarith only [h4336, h5564, hlam]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4336, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h4342, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h5120, hlam, p5481_1]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [h5121, hlam, p5481_0]
                      · have p5481_0 := h5481c.1
                        have p5481_1 := h5481c.2.1
                        have p5481_2 := h5481c.2.2.1
                        have p5481_3 := h5481c.2.2.2
                        linarith only [hlam, p5481_0]
                    · rcases h2bigk with h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c | h5576c
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h0, hlam, p5576_1]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        rcases p5576_3 (m.d 0 2) (by simp) with h5579 | h5579
                        · rcases p5576_3 (m.d 1 2) (by simp) with h5580 | h5580
                          · rcases p5576_3 (m.d 2 3) (by simp) with h5581 | h5581
                            · linarith only [h5581, hlam, p5576_0]
                            · rcases p5576_3 (m.d 2 4) (by simp) with h5583 | h5583
                              · linarith only [h4335, h5583, hlam]
                              · linarith only [h4346, h5583, hlam]
                          · linarith only [h4340, h5580, hlam]
                        · linarith only [h5579, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        rcases p5576_3 (m.d 0 2) (by simp) with h5588 | h5588
                        · rcases p5576_3 (m.d 1 2) (by simp) with h5589 | h5589
                          · rcases p5576_3 (m.d 2 3) (by simp) with h5590 | h5590
                            · linarith only [h4334, h5590, hlam]
                            · rcases p5576_3 (m.d 2 4) (by simp) with h5592 | h5592
                              · linarith only [h5592, hlam, p5576_0]
                              · rcases p5576_3 (m.d 2 5) (by simp) with h5594 | h5594
                                · linarith only [h4336, h5594, hlam]
                                · rcases h3bigk with h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c | h5596c
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h3609, hlam, p5596_1]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    rcases p5596_3 (m.d 0 3) (by simp) with h5599 | h5599
                                    · rcases p5596_3 (m.d 1 3) (by simp) with h5600 | h5600
                                      · rcases p5596_3 (m.d 2 3) (by simp) with h5601 | h5601
                                        · linarith only [h4334, h5601, hlam]
                                        · rcases p5596_3 (m.d 3 4) (by simp) with h5603 | h5603
                                          · linarith only [h4337, h5603, hlam]
                                          · linarith only [h4346, h5603, hlam]
                                      · linarith only [h4340, h5600, hlam]
                                    · linarith only [h4334, h5599, hlam]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h0, h4334, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5596_1]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4333, h4337, h4342, h5120, hlam, p5123_1, p5596_2]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4340, h5479, hc12, hlam, ht01, p5596_1]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    rcases p5596_3 (m.d 0 3) (by simp) with h5612 | h5612
                                    · linarith only [h3609, h5612, hlam]
                                    · linarith only [h4334, h5612, hlam]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5596_1]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h3609, h4333, h4337, h4342, h5120, hlam, p5123_1, p5596_2]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4334, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4340, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4346, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4337, h4346, h5122, hc03, hc45, hlam, hphi, ht0b, ht5b, p5596_1]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4337, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4343, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h0, h4334, h4337, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5596_1]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    rcases p5596_3 (m.d 0 3) (by simp) with h5626 | h5626
                                    · rcases p5596_3 (m.d 1 3) (by simp) with h5627 | h5627
                                      · rcases p5596_3 (m.d 2 3) (by simp) with h5628 | h5628
                                        · linarith only [h4346, h5628, hlam]
                                        · linarith only [h5120, h5628, hlam]
                                      · linarith only [h4344, h5627, hlam]
                                    · linarith only [h4338, h5626, hlam]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4338, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h4344, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h5120, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [h5122, hlam, p5596_0]
                                  · have p5596_0 := h5596c.1
                                    have p5596_1 := h5596c.2.1
                                    have p5596_2 := h5596c.2.2.1
                                    have p5596_3 := h5596c.2.2.2
                                    linarith only [hlam, p5596_0]
                          · linarith only [h4341, h5589, hlam]
                        · linarith only [h5588, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4333, h4335, h4342, hlam, p5123_1, p5576_2]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4334, h5479, hc12, hlam, ht01, p5576_1]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        rcases p5576_3 (m.d 0 2) (by simp) with h5643 | h5643
                        · linarith only [h0, h5643, hlam]
                        · linarith only [h4334, h5643, hlam]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        rcases p5576_3 (m.d 0 2) (by simp) with h5646 | h5646
                        · linarith only [h0, h5646, hlam]
                        · linarith only [h4335, h5646, hlam]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h0, h4333, h4334, h4337, h4342, hlam, p5123_1, p5576_2]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4334, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4340, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4346, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4334, h4337, h4346, h5120, h5122, hc02, hc45, hlam, hphi, ht0b, ht5b, p5576_1]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4335, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4341, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h0, h4335, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5576_1]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        rcases p5576_3 (m.d 0 2) (by simp) with h5659 | h5659
                        · rcases p5576_3 (m.d 1 2) (by simp) with h5660 | h5660
                          · rcases p5576_3 (m.d 2 3) (by simp) with h5661 | h5661
                            · linarith only [h4346, h5661, hlam]
                            · linarith only [h5120, h5661, hlam]
                          · linarith only [h4342, h5660, hlam]
                        · linarith only [h4336, h5659, hlam]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4336, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h4342, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h5120, hlam, p5576_1]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [h5121, hlam, p5576_0]
                      · have p5576_0 := h5576c.1
                        have p5576_1 := h5576c.2.1
                        have p5576_2 := h5576c.2.2.1
                        have p5576_3 := h5576c.2.2.2
                        linarith only [hlam, p5576_0]
                    · rcases h2bigk with h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c | h5671c
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h0, hlam, p5671_1]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        rcases p5671_3 (m.d 0 2) (by simp) with h5674 | h5674
                        · rcases p5671_3 (m.d 1 2) (by simp) with h5675 | h5675
                          · rcases p5671_3 (m.d 2 3) (by simp) with h5676 | h5676
                            · linarith only [h5676, hlam, p5671_0]
                            · rcases p5671_3 (m.d 2 4) (by simp) with h5678 | h5678
                              · linarith only [h4335, h5678, hlam]
                              · linarith only [h4346, h5678, hlam]
                          · linarith only [h4340, h5675, hlam]
                        · linarith only [h5674, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        rcases p5671_3 (m.d 0 2) (by simp) with h5683 | h5683
                        · rcases p5671_3 (m.d 1 2) (by simp) with h5684 | h5684
                          · rcases p5671_3 (m.d 2 3) (by simp) with h5685 | h5685
                            · linarith only [h4334, h5685, hlam]
                            · rcases p5671_3 (m.d 2 4) (by simp) with h5687 | h5687
                              · linarith only [h5687, hlam, p5671_0]
                              · rcases p5671_3 (m.d 2 5) (by simp) with h5689 | h5689
                                · linarith only [h4336, h5689, hlam]
                                · rcases h3bigk with h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h3609, hlam, p5691_1]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    rcases p5691_3 (m.d 0 3) (by simp) with h5694 | h5694
                                    · rcases p5691_3 (m.d 1 3) (by simp) with h5695 | h5695
                                      · rcases p5691_3 (m.d 2 3) (by simp) with h5696 | h5696
                                        · linarith only [h4334, h5696, hlam]
                                        · rcases p5691_3 (m.d 3 4) (by simp) with h5698 | h5698
                                          · linarith only [h4337, h5698, hlam]
                                          · linarith only [h4346, h5698, hlam]
                                      · linarith only [h4340, h5695, hlam]
                                    · linarith only [h4334, h5694, hlam]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h0, h4334, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5691_1]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4333, h4337, h4342, h5120, hlam, p5123_1, p5691_2]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4333, h4337, h4340, h4342, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5123_1, p5691_1]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    rcases p5691_3 (m.d 0 3) (by simp) with h5707 | h5707
                                    · linarith only [h3609, h5707, hlam]
                                    · linarith only [h4334, h5707, hlam]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4340, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5691_1]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h3609, h4333, h4337, h4342, h5120, hlam, p5123_1, p5691_2]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4334, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4340, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4346, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4337, h4346, h5122, hc03, hc45, hlam, hphi, ht0b, ht5b, p5691_1]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4337, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4343, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h0, h4334, h4337, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5691_1]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    rcases p5691_3 (m.d 0 3) (by simp) with h5721 | h5721
                                    · rcases p5691_3 (m.d 1 3) (by simp) with h5722 | h5722
                                      · rcases p5691_3 (m.d 2 3) (by simp) with h5723 | h5723
                                        · linarith only [h4346, h5723, hlam]
                                        · linarith only [h5120, h5723, hlam]
                                      · linarith only [h4344, h5722, hlam]
                                    · linarith only [h4338, h5721, hlam]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4338, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h4344, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h5120, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [h5122, hlam, p5691_0]
                                  · have p5691_0 := h5691c.1
                                    have p5691_1 := h5691c.2.1
                                    have p5691_2 := h5691c.2.2.1
                                    have p5691_3 := h5691c.2.2.2
                                    linarith only [hlam, p5691_0]
                          · linarith only [h4341, h5684, hlam]
                        · linarith only [h5683, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4333, h4335, h4342, hlam, p5123_1, p5671_2]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4334, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5671_1]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        rcases p5671_3 (m.d 0 2) (by simp) with h5738 | h5738
                        · linarith only [h0, h5738, hlam]
                        · linarith only [h4334, h5738, hlam]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        rcases p5671_3 (m.d 0 2) (by simp) with h5741 | h5741
                        · linarith only [h0, h5741, hlam]
                        · linarith only [h4335, h5741, hlam]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h0, h4333, h4334, h4337, h4342, hlam, p5123_1, p5671_2]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4334, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4340, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4346, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4334, h4337, h4346, h5120, h5122, hc02, hc45, hlam, hphi, ht0b, ht5b, p5671_1]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4335, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4341, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h0, h4334, h4337, h4346, h5120, h5122, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5671_1]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        rcases p5671_3 (m.d 0 2) (by simp) with h5754 | h5754
                        · rcases p5671_3 (m.d 1 2) (by simp) with h5755 | h5755
                          · rcases p5671_3 (m.d 2 3) (by simp) with h5756 | h5756
                            · linarith only [h4346, h5756, hlam]
                            · linarith only [h5120, h5756, hlam]
                          · linarith only [h4342, h5755, hlam]
                        · linarith only [h4336, h5754, hlam]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4336, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h4342, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h5120, hlam, p5671_1]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [h5121, hlam, p5671_0]
                      · have p5671_0 := h5671c.1
                        have p5671_1 := h5671c.2.1
                        have p5671_2 := h5671c.2.2.1
                        have p5671_3 := h5671c.2.2.2
                        linarith only [hlam, p5671_0]
                    · linarith only [h5479, hlam, ht01, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h4113, h5476, hlam]
              · linarith only [h3609, h5475, hlam]
            · linarith only [h0, h5474, hlam]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4335, hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4337, hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          rcases p5123_3 (m.d 0 1) (by simp) with h5773 | h5773
          · linarith only [h4113, h5773, hlam]
          · linarith only [h4333, h5773, hlam]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4333, hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4336, hlam, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4338, hlam, p5123_0]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [h4339, hlam, p5123_1]
        · have p5123_0 := h5123c.1
          have p5123_1 := h5123c.2.1
          have p5123_2 := h5123c.2.2.1
          have p5123_3 := h5123c.2.2.2
          linarith only [hlam, p5123_0]
      · linarith only [h4346, h5122, hc24, hlam, hphi, ht45, u5elo4]
    · linarith only [h4345, h4346, h5121, hc23, hlam, hphi, ht34, ht45, u5elo1]
  · linarith only [h5120, hc23, hlam, hphi, ht34, ht45, u5elo3]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4344 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4345 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 2 3 4 (by decide) (by decide) with h4346 | h4346
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343 h4344 h4345 h4346
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343 h4344 h4345 h4346

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4344 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4345 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h4345, hc14, hlam, hphi, ht45, u5elo4]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4344 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 1 4 5 (by decide) (by decide) with h4345 | h4345
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343 h4344 h4345
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343 h4344 h4345

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4344 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  linarith only [h4344, hc13, hlam, hphi, ht34, ht45, u5elo3]

set_option maxHeartbeats 5024000 in
set_option maxHeartbeats 5024000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3609 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4113 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4333 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4334 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4335 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4336 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4340 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4341 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h4342 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h4343 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h3609 := hg3609
  have h4113 := hg4113
  have h4333 := hg4333
  rcases m.htr 1 3 5 (by decide) (by decide) with h4344 | h4344
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343 h4344
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_L_s7_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg3609 hg4113 hg4333 h4334 h4335 h4336 h4337 h4338 h4339 h4340 h4341 h4342 h4343 h4344

end R2N4
