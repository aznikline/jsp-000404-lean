import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h4561 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 4 5 (by decide) (by decide) with h5170 | h5170
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5171 | h5171
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5172 | h5172
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5173 | h5173
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5174 | h5174
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5175 | h5175
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5176 | h5176
              · linarith only [h4558, h4561, h5176, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5178 | h5178
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5179 | h5179
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5180 | h5180
                    · linarith only [h4558, h4561, h5171, h5174, h5178, h5180, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h4561, h5170, h5180, hlam]
                  · linarith only [h4561, h5170, h5171, h5174, h5179, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5184 | h5184
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5185 | h5185
                    · rcases h2bigk with h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c | h5186c
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h0, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        rcases p5186_3 (m.d 0 2) (by simp) with h5189 | h5189
                        · rcases p5186_3 (m.d 1 2) (by simp) with h5190 | h5190
                          · rcases p5186_3 (m.d 2 3) (by simp) with h5191 | h5191
                            · linarith only [h5191, hlam, p5186_0]
                            · rcases p5186_3 (m.d 2 4) (by simp) with h5193 | h5193
                              · linarith only [h4559, h5193, hlam]
                              · linarith only [h5176, h5193, hlam]
                          · linarith only [h5171, h5190, hlam]
                        · linarith only [h5189, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h0, h5184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5186_1, u4ehi4]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        rcases p5186_3 (m.d 0 2) (by simp) with h5199 | h5199
                        · rcases p5186_3 (m.d 1 2) (by simp) with h5200 | h5200
                          · rcases p5186_3 (m.d 2 3) (by simp) with h5201 | h5201
                            · linarith only [h4558, h5201, hlam]
                            · rcases p5186_3 (m.d 2 4) (by simp) with h5203 | h5203
                              · linarith only [h4559, h5203, hlam]
                              · linarith only [h5184, h5203, hlam]
                          · linarith only [h5173, h5200, hlam]
                        · linarith only [h5199, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h4559, h5184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5186_1, u4ehi4]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        rcases p5186_3 (m.d 0 2) (by simp) with h5210 | h5210
                        · linarith only [h0, h5210, hlam]
                        · linarith only [h4558, h5210, hlam]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h5184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5186_1, u4ehi4]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        rcases p5186_3 (m.d 0 2) (by simp) with h5214 | h5214
                        · linarith only [h0, h5214, hlam]
                        · linarith only [h4560, h5214, hlam]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h4558, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h5171, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h5176, hlam, p5186_1]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h5178, hlam, p5186_1]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h4559, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h5172, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        rcases p5186_3 (m.d 0 2) (by simp) with h5224 | h5224
                        · rcases p5186_3 (m.d 1 2) (by simp) with h5225 | h5225
                          · rcases p5186_3 (m.d 2 3) (by simp) with h5226 | h5226
                            · linarith only [h5176, h5226, hlam]
                            · rcases p5186_3 (m.d 2 4) (by simp) with h5228 | h5228
                              · rcases p5186_3 (m.d 2 5) (by simp) with h5229 | h5229
                                · linarith only [h5184, h5229, hlam]
                                · linarith only [h5178, h5229, hlam]
                              · linarith only [h5176, h5228, hlam]
                          · linarith only [h5171, h5225, hlam]
                        · linarith only [h4558, h5224, hlam]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h4559, h4561, h5171, h5174, h5184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5186_1, u4ehi4]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h4560, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h5173, hlam, p5186_0]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        rcases p5186_3 (m.d 0 2) (by simp) with h5239 | h5239
                        · rcases p5186_3 (m.d 1 2) (by simp) with h5240 | h5240
                          · rcases p5186_3 (m.d 2 3) (by simp) with h5241 | h5241
                            · linarith only [h5178, h5241, hlam]
                            · rcases p5186_3 (m.d 2 4) (by simp) with h5243 | h5243
                              · rcases p5186_3 (m.d 2 5) (by simp) with h5244 | h5244
                                · rcases h4bigk with h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c | h5245c
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4130, hlam, p5245_1]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4561, h5171, h5174, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5245_1, u4ehi2]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4561, hlam, p5245_1]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4561, h5171, h5174, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5245_1, u4ehi4]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4560, h5170, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5186_1, p5245_1]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5171, h5174, h5184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5245_1, u4ehi4]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4560, h4561, h5170, h5171, h5174, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5186_1, p5245_1]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    rcases p5245_3 (m.d 0 4) (by simp) with h5255 | h5255
                                    · linarith only [h4130, h5255, hlam]
                                    · linarith only [h5170, h5255, hlam]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4559, hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5172, hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5176, hlam, p5245_1]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4559, hc02, hlam, hphi, ht0b, ht45, ht5b, p5245_1, u4ehi4]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h4560, h5170, hc23, hc34, hlam, hphi, p5186_1, p5245_1]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5174, hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5171, h5174, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5245_1, u4ehi2]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5171, h5174, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5245_1, u4ehi4]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5170, hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5175, hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5184, hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [h5185, hlam, p5245_0]
                                  · have p5245_0 := h5245c.1
                                    have p5245_1 := h5245c.2.1
                                    have p5245_2 := h5245c.2.2.1
                                    have p5245_3 := h5245c.2.2.2
                                    linarith only [hlam, p5245_0]
                                · linarith only [h5178, h5244, hlam]
                              · linarith only [h5176, h5243, hlam]
                          · linarith only [h5171, h5240, hlam]
                        · linarith only [h4558, h5239, hlam]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [h5184, hlam, p5186_1]
                      · have p5186_0 := h5186c.1
                        have p5186_1 := h5186c.2.1
                        have p5186_2 := h5186c.2.2.1
                        have p5186_3 := h5186c.2.2.2
                        linarith only [hlam, p5186_0]
                    · linarith only [h4561, h5170, h5185, hlam]
                  · linarith only [h4561, h5170, h5171, h5174, h5184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h4561, h5170, h5171, h5174, h5175, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5282 | h5282
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5283 | h5283
              · linarith only [h3260, h5174, h5283, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5285 | h5285
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5286 | h5286
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5287 | h5287
                    · rcases h2bigk with h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h5285, h5287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h5283, h5285, h5287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        rcases p5288_3 (m.d 0 2) (by simp) with h5293 | h5293
                        · rcases p5288_3 (m.d 1 2) (by simp) with h5294 | h5294
                          · rcases p5288_3 (m.d 2 3) (by simp) with h5295 | h5295
                            · linarith only [h4558, h5295, hlam]
                            · linarith only [h5285, h5295, hlam]
                          · linarith only [h5173, h5294, hlam]
                        · linarith only [h5293, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4558, h5285, h5287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5285, h5287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5283, h5285, h5287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        rcases p5288_3 (m.d 0 2) (by simp) with h5304 | h5304
                        · linarith only [h0, h5304, hlam]
                        · linarith only [h4560, h5304, hlam]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4558, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5171, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5283, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4559, h5283, h5285, h5287, hc02, hlam, hphi, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4559, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5172, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4559, h5285, h5287, hc04, hlam, hphi, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h4559, h5285, h5287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5288_1, u4ehi4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4560, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5173, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5285, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5286, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                    · linarith only [h3260, h5174, h5287, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h5283, h5285, h5286, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5324 | h5324
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5325 | h5325
                    · rcases h2bigk with h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c | h5326c
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h0, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        rcases p5326_3 (m.d 0 2) (by simp) with h5329 | h5329
                        · rcases p5326_3 (m.d 1 2) (by simp) with h5330 | h5330
                          · rcases p5326_3 (m.d 2 3) (by simp) with h5331 | h5331
                            · linarith only [h5331, hlam, p5326_0]
                            · rcases p5326_3 (m.d 2 4) (by simp) with h5333 | h5333
                              · linarith only [h4559, h5333, hlam]
                              · linarith only [h5283, h5333, hlam]
                          · linarith only [h5171, h5330, hlam]
                        · linarith only [h5329, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h0, h5324, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5326_1, u4ehi4]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        rcases p5326_3 (m.d 0 2) (by simp) with h5339 | h5339
                        · rcases p5326_3 (m.d 1 2) (by simp) with h5340 | h5340
                          · rcases p5326_3 (m.d 2 3) (by simp) with h5341 | h5341
                            · linarith only [h4558, h5341, hlam]
                            · rcases p5326_3 (m.d 2 4) (by simp) with h5343 | h5343
                              · linarith only [h4559, h5343, hlam]
                              · linarith only [h5324, h5343, hlam]
                          · linarith only [h5173, h5340, hlam]
                        · linarith only [h5339, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h4559, h5324, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5326_1, u4ehi4]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        rcases p5326_3 (m.d 0 2) (by simp) with h5350 | h5350
                        · linarith only [h0, h5350, hlam]
                        · linarith only [h4558, h5350, hlam]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h5324, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5326_1, u4ehi4]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        rcases p5326_3 (m.d 0 2) (by simp) with h5354 | h5354
                        · linarith only [h0, h5354, hlam]
                        · linarith only [h4560, h5354, hlam]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h4558, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h5171, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h5283, hlam, p5326_1]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h5285, hlam, p5326_1]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h4559, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h5172, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        rcases p5326_3 (m.d 0 2) (by simp) with h5364 | h5364
                        · rcases p5326_3 (m.d 1 2) (by simp) with h5365 | h5365
                          · rcases p5326_3 (m.d 2 3) (by simp) with h5366 | h5366
                            · linarith only [h5283, h5366, hlam]
                            · rcases p5326_3 (m.d 2 4) (by simp) with h5368 | h5368
                              · rcases p5326_3 (m.d 2 5) (by simp) with h5369 | h5369
                                · linarith only [h5324, h5369, hlam]
                                · linarith only [h5285, h5369, hlam]
                              · linarith only [h5283, h5368, hlam]
                          · linarith only [h5171, h5365, hlam]
                        · linarith only [h4558, h5364, hlam]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h4559, h5324, hc02, hlam, hphi, ht0b, ht45, ht5b, p5326_1, u4ehi4]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h4560, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h5173, hlam, p5326_0]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        rcases p5326_3 (m.d 0 2) (by simp) with h5379 | h5379
                        · rcases p5326_3 (m.d 1 2) (by simp) with h5380 | h5380
                          · rcases p5326_3 (m.d 2 3) (by simp) with h5381 | h5381
                            · linarith only [h5285, h5381, hlam]
                            · rcases p5326_3 (m.d 2 4) (by simp) with h5383 | h5383
                              · rcases p5326_3 (m.d 2 5) (by simp) with h5384 | h5384
                                · rcases h4bigk with h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h4130, hlam, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h4130, h5174, h5324, hc23, hc34, hlam, hphi, p5326_1, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h4561, hlam, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    rcases p5385_3 (m.d 0 4) (by simp) with h5390 | h5390
                                    · rcases p5385_3 (m.d 1 4) (by simp) with h5391 | h5391
                                      · rcases p5385_3 (m.d 2 4) (by simp) with h5392 | h5392
                                        · linarith only [h4559, h5392, hlam]
                                        · linarith only [h5324, h5392, hlam]
                                      · linarith only [h5282, h5391, hlam]
                                    · linarith only [h5390, hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h4559, h5174, h5324, hc23, hc34, hlam, hphi, p5326_1, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5174, h5324, hc23, hc34, hlam, hphi, p5326_1, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5174, hlam, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    rcases p5385_3 (m.d 0 4) (by simp) with h5401 | h5401
                                    · linarith only [h4130, h5401, hlam]
                                    · linarith only [h5170, h5401, hlam]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h4559, hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5172, hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5283, hlam, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h0, h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5385_1, u4ehi4]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h4559, h5324, hc23, hc34, hlam, hphi, p5326_1, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h0, h4130, h4559, h5324, hc01, hc12, hc23, hc34, hlam, hphi, p5326_1, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5324, hc23, hc34, hlam, hphi, p5326_1, p5385_1]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    rcases p5385_3 (m.d 0 4) (by simp) with h5413 | h5413
                                    · linarith only [h4561, h5413, hlam]
                                    · linarith only [h5170, h5413, hlam]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5170, hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5282, hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5324, hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [h5325, hlam, p5385_0]
                                  · have p5385_0 := h5385c.1
                                    have p5385_1 := h5385c.2.1
                                    have p5385_2 := h5385c.2.2.1
                                    have p5385_3 := h5385c.2.2.2
                                    linarith only [hlam, p5385_0]
                                · linarith only [h5285, h5384, hlam]
                              · linarith only [h5283, h5383, hlam]
                          · linarith only [h5171, h5380, hlam]
                        · linarith only [h4558, h5379, hlam]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [h5324, hlam, p5326_1]
                      · have p5326_0 := h5326c.1
                        have p5326_1 := h5326c.2.1
                        have p5326_2 := h5326c.2.2.1
                        have p5326_3 := h5326c.2.2.2
                        linarith only [hlam, p5326_0]
                    · linarith only [h4561, h5170, h5325, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5428 | h5428
                    · rcases h2bigk with h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c | h5429c
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h0, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        rcases p5429_3 (m.d 0 2) (by simp) with h5432 | h5432
                        · rcases p5429_3 (m.d 1 2) (by simp) with h5433 | h5433
                          · rcases p5429_3 (m.d 2 3) (by simp) with h5434 | h5434
                            · linarith only [h5434, hlam, p5429_0]
                            · rcases p5429_3 (m.d 2 4) (by simp) with h5436 | h5436
                              · linarith only [h4559, h5436, hlam]
                              · linarith only [h5283, h5436, hlam]
                          · linarith only [h5171, h5433, hlam]
                        · linarith only [h5432, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        rcases p5429_3 (m.d 0 2) (by simp) with h5441 | h5441
                        · rcases p5429_3 (m.d 1 2) (by simp) with h5442 | h5442
                          · rcases p5429_3 (m.d 2 3) (by simp) with h5443 | h5443
                            · linarith only [h4558, h5443, hlam]
                            · rcases p5429_3 (m.d 2 4) (by simp) with h5445 | h5445
                              · linarith only [h5445, hlam, p5429_0]
                              · rcases p5429_3 (m.d 2 5) (by simp) with h5447 | h5447
                                · linarith only [h4560, h5447, hlam]
                                · linarith only [h5324, h5447, hlam]
                          · linarith only [h5172, h5442, hlam]
                        · linarith only [h5441, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        rcases p5429_3 (m.d 0 2) (by simp) with h5452 | h5452
                        · rcases p5429_3 (m.d 1 2) (by simp) with h5453 | h5453
                          · rcases p5429_3 (m.d 2 3) (by simp) with h5454 | h5454
                            · linarith only [h4558, h5454, hlam]
                            · rcases p5429_3 (m.d 2 4) (by simp) with h5456 | h5456
                              · linarith only [h4559, h5456, hlam]
                              · rcases p5429_3 (m.d 2 5) (by simp) with h5458 | h5458
                                · linarith only [h5458, hlam, p5429_0]
                                · rcases h4bigk with h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c | h5460c
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h4130, hlam, p5460_1]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    rcases p5460_3 (m.d 0 4) (by simp) with h5463 | h5463
                                    · rcases p5460_3 (m.d 1 4) (by simp) with h5464 | h5464
                                      · rcases p5460_3 (m.d 2 4) (by simp) with h5465 | h5465
                                        · linarith only [h4559, h5465, hlam]
                                        · rcases p5460_3 (m.d 3 4) (by simp) with h5467 | h5467
                                          · rcases p5460_3 (m.d 4 5) (by simp) with h5468 | h5468
                                            · linarith only [h5170, h5468, hlam]
                                            · linarith only [h5324, h5468, hlam]
                                          · linarith only [h5283, h5467, hlam]
                                      · linarith only [h5172, h5464, hlam]
                                    · linarith only [h4559, h5463, hlam]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h4561, hlam, p5460_1]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h4559, h5324, hc02, hlam, hphi, ht0b, ht45, ht5b, p5460_1, u4ehi2]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5170, h5174, h5324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5460_1, u4ehi2]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    rcases p5460_3 (m.d 0 4) (by simp) with h5478 | h5478
                                    · linarith only [h4130, h5478, hlam]
                                    · linarith only [h4559, h5478, hlam]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5174, hlam, p5460_1]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5174, h5324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5460_1, u4ehi2]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h4559, hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5172, hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5283, hlam, p5460_1]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5324, hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5170, h5324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5460_1, u4ehi2]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h4130, hc01, hc34, hlam, hphi, ht12, ht23, p5460_1]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    rcases p5460_3 (m.d 0 4) (by simp) with h5490 | h5490
                                    · linarith only [h4561, h5490, hlam]
                                    · linarith only [h4559, h5490, hlam]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5460_1, u4ehi2]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5170, hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5282, hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5170, hc04, hlam, hphi, ht0b, ht45, ht5b, p5460_1, u4ehi2]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [h5428, hlam, p5460_0]
                                  · have p5460_0 := h5460c.1
                                    have p5460_1 := h5460c.2.1
                                    have p5460_2 := h5460c.2.2.1
                                    have p5460_3 := h5460c.2.2.2
                                    linarith only [hlam, p5460_0]
                          · linarith only [h5173, h5453, hlam]
                        · linarith only [h5452, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5429_1, u4ehi2]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        rcases p5429_3 (m.d 0 2) (by simp) with h5504 | h5504
                        · linarith only [h0, h5504, hlam]
                        · linarith only [h4558, h5504, hlam]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        rcases p5429_3 (m.d 0 2) (by simp) with h5507 | h5507
                        · linarith only [h0, h5507, hlam]
                        · linarith only [h4559, h5507, hlam]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        rcases p5429_3 (m.d 0 2) (by simp) with h5510 | h5510
                        · linarith only [h0, h5510, hlam]
                        · linarith only [h4560, h5510, hlam]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h4558, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h5171, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h5283, hlam, p5429_1]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h5285, hlam, p5429_1]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h4559, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h5172, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h4130, h5170, h5174, h5324, hc23, hc34, hlam, hphi, p5429_1]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h5324, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h4560, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h5173, hlam, p5429_0]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h4130, h5170, h5174, h5324, hc23, hc34, hlam, hphi, p5429_1]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [h4130, h5170, h5174, h5324, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5429_1, u4ehi2]
                      · have p5429_0 := h5429c.1
                        have p5429_1 := h5429c.2.1
                        have p5429_2 := h5429c.2.2.1
                        have p5429_3 := h5429c.2.2.2
                        linarith only [hlam, p5429_0]
                    · linarith only [h4130, h5170, h5174, h5428, hlam]
            · linarith only [h4130, h5170, h5282, hlam]
        · linarith only [h0, h4560, h5173, hlam]
      · linarith only [h0, h4559, h5172, hlam]
    · linarith only [h0, h4558, h5171, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5533 | h5533
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5534 | h5534
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5535 | h5535
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5536 | h5536
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5537 | h5537
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5538 | h5538
              · linarith only [h4558, h4561, h5538, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5540 | h5540
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5541 | h5541
                  · linarith only [h4559, h5170, h5541, hlam]
                  · linarith only [h5538, h5540, h5541, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5544 | h5544
                  · linarith only [h4559, h5170, h5544, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5546 | h5546
                    · linarith only [h4559, h5170, h5536, h5546, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h3260, h4561, h5537, h5546, hc01, hc14, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5549 | h5549
              · linarith only [h4558, h4561, h5549, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5551 | h5551
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5552 | h5552
                  · linarith only [h0, h4359, h4559, h5537, h5552, hc01, hc12, hlam, hphi]
                  · linarith only [h4558, h4561, h5536, h5537, h5551, h5552, hc45, hlam, hphi, u4ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5555 | h5555
                  · linarith only [h3260, h4561, h5536, h5537, h5555, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5557 | h5557
                    · linarith only [h5536, h5537, h5557, hlam]
                    · rcases h2bigk with h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c | h5559c
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h0, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        rcases p5559_3 (m.d 0 2) (by simp) with h5562 | h5562
                        · rcases p5559_3 (m.d 1 2) (by simp) with h5563 | h5563
                          · rcases p5559_3 (m.d 2 3) (by simp) with h5564 | h5564
                            · linarith only [h5564, hlam, p5559_0]
                            · rcases p5559_3 (m.d 2 4) (by simp) with h5566 | h5566
                              · linarith only [h4559, h5566, hlam]
                              · linarith only [h5549, h5566, hlam]
                          · linarith only [h5533, h5563, hlam]
                        · linarith only [h5562, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        rcases p5559_3 (m.d 0 2) (by simp) with h5571 | h5571
                        · rcases p5559_3 (m.d 1 2) (by simp) with h5572 | h5572
                          · rcases p5559_3 (m.d 2 3) (by simp) with h5573 | h5573
                            · linarith only [h4558, h5573, hlam]
                            · rcases p5559_3 (m.d 2 4) (by simp) with h5575 | h5575
                              · linarith only [h5575, hlam, p5559_0]
                              · rcases p5559_3 (m.d 2 5) (by simp) with h5577 | h5577
                                · linarith only [h4560, h5577, hlam]
                                · linarith only [h5555, h5577, hlam]
                          · linarith only [h5534, h5572, hlam]
                        · linarith only [h5571, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        rcases p5559_3 (m.d 0 2) (by simp) with h5582 | h5582
                        · rcases p5559_3 (m.d 1 2) (by simp) with h5583 | h5583
                          · rcases p5559_3 (m.d 2 3) (by simp) with h5584 | h5584
                            · linarith only [h4558, h5584, hlam]
                            · rcases p5559_3 (m.d 2 4) (by simp) with h5586 | h5586
                              · linarith only [h4559, h5586, hlam]
                              · rcases p5559_3 (m.d 2 5) (by simp) with h5588 | h5588
                                · linarith only [h5588, hlam, p5559_0]
                                · rcases h4bigk with h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h4130, hlam, p5590_1]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h4561, h5536, h5537, hc45, hlam, hphi, p5590_1, u4ehi2]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h4561, hlam, p5590_1]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5170, hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5537, hc45, hlam, hphi, p5590_1, u4ehi0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5537, hc45, hlam, hphi, p5590_1, u4ehi2]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h3260, h4561, h5537, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5590_1]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5537, hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h4559, hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5534, hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5549, hlam, p5590_1]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5555, hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h4559, h5533, h5536, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5590_1, u4ehi2]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5536, hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5536, h5537, hc45, hlam, hphi, p5590_1, u4ehi2]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h5557, hlam, p5590_0]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h4559, hc45, hlam, hphi, p5590_1, u4ehi2]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [hc45, hlam, hphi, p5590_1, u4ehi1]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [hc45, hlam, hphi, p5590_1, u4ehi2]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [h3260, h4561, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5590_1]
                                  · have p5590_0 := h5590c.1
                                    have p5590_1 := h5590c.2.1
                                    have p5590_2 := h5590c.2.2.1
                                    have p5590_3 := h5590c.2.2.2
                                    linarith only [hlam, p5590_0]
                          · linarith only [h5535, h5583, hlam]
                        · linarith only [h5582, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5559_1, u4ehi2]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        rcases p5559_3 (m.d 0 2) (by simp) with h5620 | h5620
                        · linarith only [h0, h5620, hlam]
                        · linarith only [h4558, h5620, hlam]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        rcases p5559_3 (m.d 0 2) (by simp) with h5623 | h5623
                        · linarith only [h0, h5623, hlam]
                        · linarith only [h4559, h5623, hlam]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        rcases p5559_3 (m.d 0 2) (by simp) with h5626 | h5626
                        · linarith only [h0, h5626, hlam]
                        · linarith only [h4560, h5626, hlam]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h4558, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h5533, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h5549, hlam, p5559_1]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h5551, hlam, p5559_1]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h4559, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h5534, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h4559, h5170, hc23, hc45, hlam, hphi, ht34, p5559_1]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h5555, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h4560, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h5535, hlam, p5559_0]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        rcases p5559_3 (m.d 0 2) (by simp) with h5641 | h5641
                        · rcases p5559_3 (m.d 1 2) (by simp) with h5642 | h5642
                          · rcases p5559_3 (m.d 2 3) (by simp) with h5643 | h5643
                            · linarith only [h5551, h5643, hlam]
                            · rcases p5559_3 (m.d 2 4) (by simp) with h5645 | h5645
                              · linarith only [h5555, h5645, hlam]
                              · linarith only [h5549, h5645, hlam]
                          · linarith only [h5533, h5642, hlam]
                        · linarith only [h4558, h5641, hlam]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [h4560, hc02, hlam, hphi, ht0b, ht45, ht5b, p5559_1, u4ehi2]
                      · have p5559_0 := h5559c.1
                        have p5559_1 := h5559c.2.1
                        have p5559_2 := h5559c.2.2.1
                        have p5559_3 := h5559c.2.2.2
                        linarith only [hlam, p5559_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5652 | h5652
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5653 | h5653
              · linarith only [h3260, h5536, h5653, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5655 | h5655
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5656 | h5656
                  · linarith only [h4559, h5170, h5656, hlam]
                  · linarith only [h5653, h5655, h5656, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5659 | h5659
                  · linarith only [h0, h4559, h5170, h5659, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5661 | h5661
                    · rcases h2bigk with h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c | h5662c
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h0, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        rcases p5662_3 (m.d 0 2) (by simp) with h5665 | h5665
                        · rcases p5662_3 (m.d 1 2) (by simp) with h5666 | h5666
                          · rcases p5662_3 (m.d 2 3) (by simp) with h5667 | h5667
                            · linarith only [h5667, hlam, p5662_0]
                            · rcases p5662_3 (m.d 2 4) (by simp) with h5669 | h5669
                              · linarith only [h4559, h5669, hlam]
                              · linarith only [h5653, h5669, hlam]
                          · linarith only [h5533, h5666, hlam]
                        · linarith only [h5665, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        rcases p5662_3 (m.d 0 2) (by simp) with h5674 | h5674
                        · rcases p5662_3 (m.d 1 2) (by simp) with h5675 | h5675
                          · rcases p5662_3 (m.d 2 3) (by simp) with h5676 | h5676
                            · linarith only [h4558, h5676, hlam]
                            · rcases p5662_3 (m.d 2 4) (by simp) with h5678 | h5678
                              · linarith only [h5678, hlam, p5662_0]
                              · rcases p5662_3 (m.d 2 5) (by simp) with h5680 | h5680
                                · linarith only [h4560, h5680, hlam]
                                · linarith only [h5659, h5680, hlam]
                          · linarith only [h5534, h5675, hlam]
                        · linarith only [h5674, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        rcases p5662_3 (m.d 0 2) (by simp) with h5685 | h5685
                        · rcases p5662_3 (m.d 1 2) (by simp) with h5686 | h5686
                          · rcases p5662_3 (m.d 2 3) (by simp) with h5687 | h5687
                            · linarith only [h4558, h5687, hlam]
                            · rcases p5662_3 (m.d 2 4) (by simp) with h5689 | h5689
                              · linarith only [h4559, h5689, hlam]
                              · rcases p5662_3 (m.d 2 5) (by simp) with h5691 | h5691
                                · linarith only [h5691, hlam, p5662_0]
                                · rcases h4bigk with h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c | h5693c
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h4130, hlam, p5693_1]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5170, h5536, h5652, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5693_1, u4ehi2]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h4561, hlam, p5693_1]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5170, hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    rcases p5693_3 (m.d 0 4) (by simp) with h5699 | h5699
                                    · linarith only [h4130, h5699, hlam]
                                    · rcases p5693_3 (m.d 1 4) (by simp) with h5701 | h5701
                                      · rcases p5693_3 (m.d 2 4) (by simp) with h5702 | h5702
                                        · linarith only [h5534, h5702, hlam]
                                        · rcases p5693_3 (m.d 3 4) (by simp) with h5704 | h5704
                                          · rcases p5693_3 (m.d 4 5) (by simp) with h5705 | h5705
                                            · linarith only [h5652, h5705, hlam]
                                            · linarith only [h5170, h5705, hlam]
                                          · linarith only [h4561, h5704, hlam]
                                      · linarith only [h4130, h5701, hlam]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    rcases p5693_3 (m.d 0 4) (by simp) with h5711 | h5711
                                    · linarith only [h4130, h5711, hlam]
                                    · linarith only [h4559, h5711, hlam]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5536, hlam, p5693_1]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5170, h5536, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5693_1, u4ehi0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h4559, hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5534, hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5653, hlam, p5693_1]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5659, hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    rcases p5693_3 (m.d 0 4) (by simp) with h5721 | h5721
                                    · linarith only [h4561, h5721, hlam]
                                    · rcases p5693_3 (m.d 1 4) (by simp) with h5723 | h5723
                                      · linarith only [h5536, h5723, hlam]
                                      · linarith only [h4130, h5723, hlam]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h4130, hc01, hc34, hlam, hphi, ht12, ht23, p5693_1]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    rcases p5693_3 (m.d 0 4) (by simp) with h5727 | h5727
                                    · linarith only [h4561, h5727, hlam]
                                    · linarith only [h4559, h5727, hlam]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h4559, h5170, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5693_1, u4ehi2]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h4559, h5652, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5693_1, u4ehi2]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5652, hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5536, h5652, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5693_1, u4ehi2]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [h5661, hlam, p5693_0]
                                  · have p5693_0 := h5693c.1
                                    have p5693_1 := h5693c.2.1
                                    have p5693_2 := h5693c.2.2.1
                                    have p5693_3 := h5693c.2.2.2
                                    linarith only [hlam, p5693_0]
                          · linarith only [h5535, h5686, hlam]
                        · linarith only [h5685, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h4559, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5662_1, u4ehi2]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        rcases p5662_3 (m.d 0 2) (by simp) with h5741 | h5741
                        · linarith only [h0, h5741, hlam]
                        · linarith only [h4558, h5741, hlam]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        rcases p5662_3 (m.d 0 2) (by simp) with h5744 | h5744
                        · linarith only [h0, h5744, hlam]
                        · linarith only [h4559, h5744, hlam]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        rcases p5662_3 (m.d 0 2) (by simp) with h5747 | h5747
                        · linarith only [h0, h5747, hlam]
                        · linarith only [h4560, h5747, hlam]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h4558, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h5533, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h5653, hlam, p5662_1]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h5655, hlam, p5662_1]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h4559, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h5534, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h4559, h5170, h5536, h5652, hc23, hc34, hlam, hphi, p5662_1]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h5659, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h4560, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h5535, hlam, p5662_0]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h4560, h5170, h5536, h5652, hc23, hc34, hlam, hphi, p5662_1]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [h4560, h5170, h5536, h5652, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5662_1, u4ehi2]
                      · have p5662_0 := h5662c.1
                        have p5662_1 := h5662c.2.1
                        have p5662_2 := h5662c.2.2.1
                        have p5662_3 := h5662c.2.2.2
                        linarith only [hlam, p5662_0]
                    · linarith only [h5536, h5652, h5661, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5766 | h5766
              · linarith only [h3260, h4558, h5536, h5652, h5766, hc45, hlam, hphi, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5768 | h5768
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5769 | h5769
                  · linarith only [h3260, h5536, h5652, h5769, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h5766, h5768, h5769, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5772 | h5772
                  · linarith only [h3260, h5536, h5652, h5772, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5774 | h5774
                    · linarith only [h3260, h5536, h5652, h5774, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h3260, h5536, h5774, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h4560, h5535, hlam]
      · linarith only [h0, h4559, h5534, hlam]
    · linarith only [h0, h4558, h5533, hlam]

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 3 4 (by decide) (by decide) with h4561 | h4561
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x0_x0 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558 h4559 h4560 h4561
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x0_x1 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558 h4559 h4560 h4561

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4560 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 3 4 (by decide) (by decide) with h5780 | h5780
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5781 | h5781
    · linarith only [h4558, h4560, h5780, h5781, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5783 | h5783
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5784 | h5784
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5785 | h5785
          · linarith only [h4559, h4560, h5785, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5787 | h5787
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5788 | h5788
              · linarith only [h5781, h5784, h5785, h5788, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5790 | h5790
                · linarith only [h0, h4558, h5785, h5790, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5792 | h5792
                  · linarith only [h3260, h5780, h5783, h5785, h5790, h5792, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h3260, h5780, h5783, h5785, h5790, h5792, hc23, hc35, hlam, hphi]
            · linarith only [h3260, h5780, h5787, hlam]
        · linarith only [h0, h4559, h5784, hlam]
      · linarith only [h0, h4558, h5783, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5798 | h5798
    · linarith only [h4559, h4560, h5798, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5800 | h5800
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5801 | h5801
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5802 | h5802
          · linarith only [h4559, h4560, h5802, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5804 | h5804
            · linarith only [h3260, h5780, h5800, h5802, h5804, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5806 | h5806
              · linarith only [h5798, h5801, h5802, h5806, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5808 | h5808
                · linarith only [h3260, h5804, h5808, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5810 | h5810
                  · linarith only [h0, h3260, h4558, h4559, h5802, h5804, h5810, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5812 | h5812
                    · linarith only [h3260, h4559, h5804, h5806, h5812, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h4559, h5802, h5812, hc45, hlam, hphi, u4ehi2]
        · linarith only [h0, h4559, h5801, hlam]
      · linarith only [h0, h4558, h5800, hlam]

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 2 5 (by decide) (by decide) with h4560 | h4560
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x0 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558 h4559 h4560
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0_x1 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558 h4559 h4560

end R2N4
