import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5090000 in
set_option maxHeartbeats 5090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg4023 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4106 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4107 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h4108 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  have h4023 := hg4023
  rcases m.htr 1 2 3 (by decide) (by decide) with h4109 | h4109
  · linarith only [h0, h4, h4109, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4111 | h4111
    · linarith only [h0, h3476, h4111, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4113 | h4113
      · linarith only [h0, h4023, h4113, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4115 | h4115
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4116 | h4116
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4117 | h4117
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4118 | h4118
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4119 | h4119
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4120 | h4120
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4121 | h4121
                    · linarith only [h1, h4115, h4121, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h0bigk with h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        rcases p4123_3 (m.d 0 1) (by simp) with h4125 | h4125
                        · rcases p4123_3 (m.d 0 2) (by simp) with h4126 | h4126
                          · linarith only [h0, h4126, hlam]
                          · rcases p4123_3 (m.d 0 3) (by simp) with h4128 | h4128
                            · linarith only [h1, h4128, hlam]
                            · linarith only [h4, h4128, hlam]
                        · linarith only [h0, h4125, hlam]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h1, h4115, h4117, h4121, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4123_1]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h2, h4117, h4121, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4123_1]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        rcases p4123_3 (m.d 0 1) (by simp) with h4134 | h4134
                        · rcases p4123_3 (m.d 0 2) (by simp) with h4135 | h4135
                          · linarith only [h0, h4135, hlam]
                          · rcases p4123_3 (m.d 0 3) (by simp) with h4137 | h4137
                            · linarith only [h1, h4137, hlam]
                            · linarith only [h4107, h4137, hlam]
                        · linarith only [h3, h4134, hlam]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h0, hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h4, hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h3476, hlam, p4123_1]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h4023, hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h1, hlam, p4123_1]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        rcases p4123_3 (m.d 0 1) (by simp) with h4147 | h4147
                        · rcases p4123_3 (m.d 0 2) (by simp) with h4148 | h4148
                          · linarith only [h4, h4148, hlam]
                          · rcases p4123_3 (m.d 0 3) (by simp) with h4150 | h4150
                            · rcases p4123_3 (m.d 0 4) (by simp) with h4151 | h4151
                              · linarith only [h4106, h4151, hlam]
                              · linarith only [h3476, h4151, hlam]
                            · linarith only [h4, h4150, hlam]
                        · linarith only [h0, h4147, hlam]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h2, h4, h4117, h4121, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4123_1]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        rcases p4123_3 (m.d 0 1) (by simp) with h4158 | h4158
                        · rcases p4123_3 (m.d 0 2) (by simp) with h4159 | h4159
                          · linarith only [h4, h4159, hlam]
                          · rcases p4123_3 (m.d 0 3) (by simp) with h4161 | h4161
                            · rcases p4123_3 (m.d 0 4) (by simp) with h4162 | h4162
                              · linarith only [h4106, h4162, hlam]
                              · linarith only [h4108, h4162, hlam]
                            · linarith only [h4107, h4161, hlam]
                        · linarith only [h3, h4158, hlam]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h2, hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        rcases p4123_3 (m.d 0 1) (by simp) with h4168 | h4168
                        · rcases p4123_3 (m.d 0 2) (by simp) with h4169 | h4169
                          · linarith only [h3476, h4169, hlam]
                          · rcases p4123_3 (m.d 0 3) (by simp) with h4171 | h4171
                            · rcases p4123_3 (m.d 0 4) (by simp) with h4172 | h4172
                              · rcases p4123_3 (m.d 0 5) (by simp) with h4173 | h4173
                                · linarith only [h4108, h4173, hlam]
                                · linarith only [h4023, h4173, hlam]
                              · linarith only [h3476, h4172, hlam]
                            · linarith only [h4, h4171, hlam]
                        · linarith only [h0, h4168, hlam]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h4106, hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        rcases p4123_3 (m.d 0 1) (by simp) with h4181 | h4181
                        · rcases p4123_3 (m.d 0 2) (by simp) with h4182 | h4182
                          · linarith only [h3476, h4182, hlam]
                          · rcases p4123_3 (m.d 0 3) (by simp) with h4184 | h4184
                            · rcases p4123_3 (m.d 0 4) (by simp) with h4185 | h4185
                              · rcases p4123_3 (m.d 0 5) (by simp) with h4186 | h4186
                                · linarith only [h4108, h4186, hlam]
                                · rcases h2bigk with h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h3476, h4023, h4118, hc12, hc23, hlam, hphi, p4123_1, p4188_1]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h3476, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4023, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h0, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4109, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4111, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4113, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    rcases p4188_3 (m.d 0 2) (by simp) with h4199 | h4199
                                    · linarith only [h4199, hlam, p4188_0]
                                    · rcases p4188_3 (m.d 1 2) (by simp) with h4201 | h4201
                                      · linarith only [h4109, h4201, hlam]
                                      · rcases p4188_3 (m.d 2 3) (by simp) with h4203 | h4203
                                        · rcases p4188_3 (m.d 2 4) (by simp) with h4204 | h4204
                                          · linarith only [h4118, h4204, hlam]
                                          · linarith only [h3476, h4204, hlam]
                                        · linarith only [h4203, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    rcases p4188_3 (m.d 0 2) (by simp) with h4208 | h4208
                                    · linarith only [h4, h4208, hlam]
                                    · linarith only [h0, h4208, hlam]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h3476, h4023, hc02, hc23, hlam, hphi, p4123_1, p4188_1]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h0, h4023, hc12, hc23, hlam, hphi, p4188_1]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    rcases p4188_3 (m.d 0 2) (by simp) with h4214 | h4214
                                    · linarith only [h4214, hlam, p4188_0]
                                    · rcases p4188_3 (m.d 1 2) (by simp) with h4216 | h4216
                                      · linarith only [h4111, h4216, hlam]
                                      · rcases p4188_3 (m.d 2 3) (by simp) with h4218 | h4218
                                        · rcases p4188_3 (m.d 2 4) (by simp) with h4219 | h4219
                                          · rcases p4188_3 (m.d 2 5) (by simp) with h4220 | h4220
                                            · linarith only [h4120, h4220, hlam]
                                            · linarith only [h4023, h4220, hlam]
                                          · linarith only [h4219, hlam, p4188_0]
                                        · linarith only [h4, h4218, hlam]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    rcases p4188_3 (m.d 0 2) (by simp) with h4225 | h4225
                                    · linarith only [h3476, h4225, hlam]
                                    · linarith only [h0, h4225, hlam]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4118, hlam, p4188_1]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h0, h4023, hc12, hc24, hlam, hphi, p4188_1]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    rcases p4188_3 (m.d 0 2) (by simp) with h4231 | h4231
                                    · linarith only [h4231, hlam, p4188_0]
                                    · rcases p4188_3 (m.d 1 2) (by simp) with h4233 | h4233
                                      · linarith only [h4113, h4233, hlam]
                                      · rcases p4188_3 (m.d 2 3) (by simp) with h4235 | h4235
                                        · rcases p4188_3 (m.d 2 4) (by simp) with h4236 | h4236
                                          · rcases p4188_3 (m.d 2 5) (by simp) with h4237 | h4237
                                            · rcases h3bigk with h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4, h4115, h4117, h4121, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4238_1]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4, hlam, p4238_1]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h3, h4106, h4117, h4121, hlam, p4123_1, p4238_2]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                rcases p4238_3 (m.d 0 3) (by simp) with h4243 | h4243
                                                · rcases p4238_3 (m.d 1 3) (by simp) with h4244 | h4244
                                                  · linarith only [h1, h4244, hlam]
                                                  · linarith only [h4116, h4244, hlam]
                                                · linarith only [h4243, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h1, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4109, hlam, p4238_1]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                rcases p4238_3 (m.d 0 3) (by simp) with h4251 | h4251
                                                · rcases p4238_3 (m.d 1 3) (by simp) with h4252 | h4252
                                                  · rcases p4238_3 (m.d 2 3) (by simp) with h4253 | h4253
                                                    · rcases p4238_3 (m.d 3 4) (by simp) with h4254 | h4254
                                                      · linarith only [h4254, hlam, p4238_0]
                                                      · rcases p4238_3 (m.d 3 5) (by simp) with h4256 | h4256
                                                        · linarith only [h4116, h4256, hlam]
                                                        · linarith only [h4121, h4256, hlam]
                                                    · linarith only [h4118, h4253, hlam]
                                                  · linarith only [h4252, hlam, p4238_0]
                                                · linarith only [h4106, h4251, hlam]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p4238_1, u5ehi3]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h3, h4106, h4117, h4121, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4123_1, p4238_1]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4115, h4117, h4121, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4238_1]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h3, h4, h4106, h4117, h4121, hlam, p4123_1, p4238_2]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                rcases p4238_3 (m.d 0 3) (by simp) with h4267 | h4267
                                                · linarith only [h4, h4267, hlam]
                                                · linarith only [h4107, h4267, hlam]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4106, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4115, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4118, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4121, hlam, p4238_1]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4107, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4116, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4119, hlam, p4238_0]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [h4106, h4107, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4123_1, p4238_1]
                                              · have p4238_0 := h4238c.1
                                                have p4238_1 := h4238c.2.1
                                                have p4238_2 := h4238c.2.2.1
                                                have p4238_3 := h4238c.2.2.2
                                                linarith only [hlam, p4238_0]
                                            · linarith only [h4237, hlam, p4188_0]
                                          · linarith only [h3476, h4236, hlam]
                                        · linarith only [h4, h4235, hlam]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    rcases p4188_3 (m.d 0 2) (by simp) with h4283 | h4283
                                    · linarith only [h4023, h4283, hlam]
                                    · linarith only [h0, h4283, hlam]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4119, hlam, p4188_1]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [h4120, hlam, p4188_0]
                                  · have p4188_0 := h4188c.1
                                    have p4188_1 := h4188c.2.1
                                    have p4188_2 := h4188c.2.2.1
                                    have p4188_3 := h4188c.2.2.2
                                    linarith only [hlam, p4188_0]
                              · linarith only [h4108, h4185, hlam]
                            · linarith only [h4107, h4184, hlam]
                        · linarith only [h3, h4181, hlam]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h3, hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        rcases p4123_3 (m.d 0 1) (by simp) with h4293 | h4293
                        · rcases p4123_3 (m.d 0 2) (by simp) with h4294 | h4294
                          · linarith only [h4023, h4294, hlam]
                          · rcases p4123_3 (m.d 0 3) (by simp) with h4296 | h4296
                            · rcases p4123_3 (m.d 0 4) (by simp) with h4297 | h4297
                              · rcases p4123_3 (m.d 0 5) (by simp) with h4298 | h4298
                                · rcases h2bigk with h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c | h4299c
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4123_1, p4299_1]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h3476, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4023, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h0, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4109, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4111, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4113, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    rcases p4299_3 (m.d 0 2) (by simp) with h4310 | h4310
                                    · linarith only [h4310, hlam, p4299_0]
                                    · rcases p4299_3 (m.d 1 2) (by simp) with h4312 | h4312
                                      · linarith only [h4109, h4312, hlam]
                                      · rcases p4299_3 (m.d 2 3) (by simp) with h4314 | h4314
                                        · rcases p4299_3 (m.d 2 4) (by simp) with h4315 | h4315
                                          · linarith only [h4118, h4315, hlam]
                                          · linarith only [h3476, h4315, hlam]
                                        · linarith only [h4314, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    rcases p4299_3 (m.d 0 2) (by simp) with h4319 | h4319
                                    · linarith only [h4, h4319, hlam]
                                    · linarith only [h0, h4319, hlam]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h3476, hc02, hc23, hlam, hphi, p4299_1]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h0, h4023, hc12, hc23, hlam, hphi, p4299_1]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    rcases p4299_3 (m.d 0 2) (by simp) with h4325 | h4325
                                    · linarith only [h4325, hlam, p4299_0]
                                    · rcases p4299_3 (m.d 1 2) (by simp) with h4327 | h4327
                                      · linarith only [h4111, h4327, hlam]
                                      · rcases p4299_3 (m.d 2 3) (by simp) with h4329 | h4329
                                        · rcases p4299_3 (m.d 2 4) (by simp) with h4330 | h4330
                                          · rcases p4299_3 (m.d 2 5) (by simp) with h4331 | h4331
                                            · linarith only [h4120, h4331, hlam]
                                            · linarith only [h4023, h4331, hlam]
                                          · linarith only [h4330, hlam, p4299_0]
                                        · linarith only [h4, h4329, hlam]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    rcases p4299_3 (m.d 0 2) (by simp) with h4336 | h4336
                                    · linarith only [h3476, h4336, hlam]
                                    · linarith only [h0, h4336, hlam]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4118, hlam, p4299_1]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h0, h4023, hc12, hc24, hlam, hphi, p4123_1, p4299_1]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    rcases p4299_3 (m.d 0 2) (by simp) with h4342 | h4342
                                    · linarith only [h4342, hlam, p4299_0]
                                    · rcases p4299_3 (m.d 1 2) (by simp) with h4344 | h4344
                                      · linarith only [h4113, h4344, hlam]
                                      · rcases p4299_3 (m.d 2 3) (by simp) with h4346 | h4346
                                        · rcases p4299_3 (m.d 2 4) (by simp) with h4347 | h4347
                                          · rcases p4299_3 (m.d 2 5) (by simp) with h4348 | h4348
                                            · rcases h3bigk with h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c | h4349c
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4, h4115, h4117, h4121, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4349_1]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4, hlam, p4349_1]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                rcases p4349_3 (m.d 0 3) (by simp) with h4353 | h4353
                                                · rcases p4349_3 (m.d 1 3) (by simp) with h4354 | h4354
                                                  · linarith only [h1, h4354, hlam]
                                                  · linarith only [h4115, h4354, hlam]
                                                · linarith only [h4353, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                rcases p4349_3 (m.d 0 3) (by simp) with h4358 | h4358
                                                · rcases p4349_3 (m.d 1 3) (by simp) with h4359 | h4359
                                                  · linarith only [h1, h4359, hlam]
                                                  · linarith only [h4116, h4359, hlam]
                                                · linarith only [h4358, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h1, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4109, hlam, p4349_1]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                rcases p4349_3 (m.d 0 3) (by simp) with h4366 | h4366
                                                · rcases p4349_3 (m.d 1 3) (by simp) with h4367 | h4367
                                                  · rcases p4349_3 (m.d 2 3) (by simp) with h4368 | h4368
                                                    · rcases p4349_3 (m.d 3 4) (by simp) with h4369 | h4369
                                                      · linarith only [h4369, hlam, p4349_0]
                                                      · rcases p4349_3 (m.d 3 5) (by simp) with h4371 | h4371
                                                        · linarith only [h4116, h4371, hlam]
                                                        · linarith only [h4121, h4371, hlam]
                                                    · linarith only [h4118, h4368, hlam]
                                                  · linarith only [h4367, hlam, p4349_0]
                                                · linarith only [h4106, h4366, hlam]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p4349_1, u5ehi3]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h0, h4106, h4108, hc12, hc23, hlam, hphi, p4123_1, p4349_1]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4115, h4117, h4121, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4349_1]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                rcases p4349_3 (m.d 0 3) (by simp) with h4381 | h4381
                                                · linarith only [h4, h4381, hlam]
                                                · linarith only [h4106, h4381, hlam]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                rcases p4349_3 (m.d 0 3) (by simp) with h4384 | h4384
                                                · linarith only [h4, h4384, hlam]
                                                · linarith only [h4107, h4384, hlam]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4106, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4115, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4118, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4121, hlam, p4349_1]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4107, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4116, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h4119, hlam, p4349_0]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [h1, h4116, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4349_1]
                                              · have p4349_0 := h4349c.1
                                                have p4349_1 := h4349c.2.1
                                                have p4349_2 := h4349c.2.2.1
                                                have p4349_3 := h4349c.2.2.2
                                                linarith only [hlam, p4349_0]
                                            · linarith only [h4348, hlam, p4299_0]
                                          · linarith only [h3476, h4347, hlam]
                                        · linarith only [h4, h4346, hlam]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    rcases p4299_3 (m.d 0 2) (by simp) with h4400 | h4400
                                    · linarith only [h4023, h4400, hlam]
                                    · linarith only [h0, h4400, hlam]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4119, hlam, p4299_1]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [h4120, hlam, p4299_0]
                                  · have p4299_0 := h4299c.1
                                    have p4299_1 := h4299c.2.1
                                    have p4299_2 := h4299c.2.2.1
                                    have p4299_3 := h4299c.2.2.2
                                    linarith only [hlam, p4299_0]
                                · linarith only [h4023, h4298, hlam]
                              · linarith only [h3476, h4297, hlam]
                            · linarith only [h4, h4296, hlam]
                        · linarith only [h0, h4293, hlam]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h4107, hlam, p4123_0]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [h4108, hlam, p4123_1]
                      · have p4123_0 := h4123c.1
                        have p4123_1 := h4123c.2.1
                        have p4123_2 := h4123c.2.2.1
                        have p4123_3 := h4123c.2.2.2
                        linarith only [hlam, p4123_0]
                  · linarith only [h0, h2, h3476, h4117, h4120, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h4, h4107, h4119, hlam]
              · linarith only [h4, h4106, h4118, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4416 | h4416
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4417 | h4417
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4418 | h4418
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4419 | h4419
                    · linarith only [h4115, h4117, h4419, hlam]
                    · rcases h0bigk with h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c | h4421c
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        rcases p4421_3 (m.d 0 1) (by simp) with h4423 | h4423
                        · rcases p4421_3 (m.d 0 2) (by simp) with h4424 | h4424
                          · linarith only [h0, h4424, hlam]
                          · rcases p4421_3 (m.d 0 3) (by simp) with h4426 | h4426
                            · linarith only [h1, h4426, hlam]
                            · linarith only [h4, h4426, hlam]
                        · linarith only [h0, h4423, hlam]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4106, h4108, h4117, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4108, h4115, h4117, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        rcases p4421_3 (m.d 0 1) (by simp) with h4432 | h4432
                        · rcases p4421_3 (m.d 0 2) (by simp) with h4433 | h4433
                          · linarith only [h0, h4433, hlam]
                          · rcases p4421_3 (m.d 0 3) (by simp) with h4435 | h4435
                            · linarith only [h1, h4435, hlam]
                            · linarith only [h4107, h4435, hlam]
                        · linarith only [h3, h4432, hlam]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h0, hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4, hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h3476, hlam, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4023, hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h1, hlam, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        rcases p4421_3 (m.d 0 1) (by simp) with h4445 | h4445
                        · rcases p4421_3 (m.d 0 2) (by simp) with h4446 | h4446
                          · linarith only [h4, h4446, hlam]
                          · rcases p4421_3 (m.d 0 3) (by simp) with h4448 | h4448
                            · rcases p4421_3 (m.d 0 4) (by simp) with h4449 | h4449
                              · linarith only [h4106, h4449, hlam]
                              · linarith only [h3476, h4449, hlam]
                            · linarith only [h4, h4448, hlam]
                        · linarith only [h0, h4445, hlam]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4108, h4111, h4117, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4, h4108, h4111, h4117, hc12, hc23, hlam, hphi, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h2, hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        rcases p4421_3 (m.d 0 1) (by simp) with h4458 | h4458
                        · rcases p4421_3 (m.d 0 2) (by simp) with h4459 | h4459
                          · linarith only [h3476, h4459, hlam]
                          · rcases p4421_3 (m.d 0 3) (by simp) with h4461 | h4461
                            · rcases p4421_3 (m.d 0 4) (by simp) with h4462 | h4462
                              · rcases p4421_3 (m.d 0 5) (by simp) with h4463 | h4463
                                · linarith only [h4108, h4463, hlam]
                                · linarith only [h4023, h4463, hlam]
                              · linarith only [h3476, h4462, hlam]
                            · linarith only [h4, h4461, hlam]
                        · linarith only [h0, h4458, hlam]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4106, hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h3476, h4108, h4111, h4117, hc12, hc24, hlam, hphi, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h3, hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        rcases p4421_3 (m.d 0 1) (by simp) with h4473 | h4473
                        · rcases p4421_3 (m.d 0 2) (by simp) with h4474 | h4474
                          · linarith only [h4023, h4474, hlam]
                          · rcases p4421_3 (m.d 0 3) (by simp) with h4476 | h4476
                            · rcases p4421_3 (m.d 0 4) (by simp) with h4477 | h4477
                              · rcases p4421_3 (m.d 0 5) (by simp) with h4478 | h4478
                                · rcases h2bigk with h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c | h4479c
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4421_1, p4479_1]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h3476, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4023, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h0, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4109, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4111, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4113, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    rcases p4479_3 (m.d 0 2) (by simp) with h4490 | h4490
                                    · linarith only [h4490, hlam, p4479_0]
                                    · rcases p4479_3 (m.d 1 2) (by simp) with h4492 | h4492
                                      · linarith only [h4109, h4492, hlam]
                                      · rcases p4479_3 (m.d 2 3) (by simp) with h4494 | h4494
                                        · rcases p4479_3 (m.d 2 4) (by simp) with h4495 | h4495
                                          · linarith only [h4416, h4495, hlam]
                                          · linarith only [h3476, h4495, hlam]
                                        · linarith only [h4494, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    rcases p4479_3 (m.d 0 2) (by simp) with h4499 | h4499
                                    · linarith only [h4, h4499, hlam]
                                    · linarith only [h0, h4499, hlam]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h3476, hc02, hc23, hlam, hphi, p4479_1]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h0, h4023, hc12, hc23, hlam, hphi, p4421_1, p4479_1]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    rcases p4479_3 (m.d 0 2) (by simp) with h4505 | h4505
                                    · linarith only [h4505, hlam, p4479_0]
                                    · rcases p4479_3 (m.d 1 2) (by simp) with h4507 | h4507
                                      · linarith only [h4111, h4507, hlam]
                                      · rcases p4479_3 (m.d 2 3) (by simp) with h4509 | h4509
                                        · rcases p4479_3 (m.d 2 4) (by simp) with h4510 | h4510
                                          · rcases p4479_3 (m.d 2 5) (by simp) with h4511 | h4511
                                            · linarith only [h4418, h4511, hlam]
                                            · linarith only [h4023, h4511, hlam]
                                          · linarith only [h4510, hlam, p4479_0]
                                        · linarith only [h4, h4509, hlam]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    rcases p4479_3 (m.d 0 2) (by simp) with h4516 | h4516
                                    · linarith only [h3476, h4516, hlam]
                                    · linarith only [h0, h4516, hlam]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4416, hlam, p4479_1]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h0, h4023, h4416, hc12, hc23, hlam, hphi, p4421_1, p4479_1]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    rcases p4479_3 (m.d 0 2) (by simp) with h4522 | h4522
                                    · linarith only [h4522, hlam, p4479_0]
                                    · rcases p4479_3 (m.d 1 2) (by simp) with h4524 | h4524
                                      · linarith only [h4113, h4524, hlam]
                                      · rcases p4479_3 (m.d 2 3) (by simp) with h4526 | h4526
                                        · rcases p4479_3 (m.d 2 4) (by simp) with h4527 | h4527
                                          · rcases p4479_3 (m.d 2 5) (by simp) with h4528 | h4528
                                            · rcases h3bigk with h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c | h4529c
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4, h4116, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4529_1, u5ehi3]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4, hlam, p4529_1]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                rcases p4529_3 (m.d 0 3) (by simp) with h4533 | h4533
                                                · rcases p4529_3 (m.d 1 3) (by simp) with h4534 | h4534
                                                  · linarith only [h1, h4534, hlam]
                                                  · linarith only [h4115, h4534, hlam]
                                                · linarith only [h4533, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                rcases p4529_3 (m.d 0 3) (by simp) with h4538 | h4538
                                                · rcases p4529_3 (m.d 1 3) (by simp) with h4539 | h4539
                                                  · linarith only [h1, h4539, hlam]
                                                  · linarith only [h4116, h4539, hlam]
                                                · linarith only [h4538, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h1, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4109, hlam, p4529_1]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                rcases p4529_3 (m.d 0 3) (by simp) with h4546 | h4546
                                                · rcases p4529_3 (m.d 1 3) (by simp) with h4547 | h4547
                                                  · rcases p4529_3 (m.d 2 3) (by simp) with h4548 | h4548
                                                    · rcases p4529_3 (m.d 3 4) (by simp) with h4549 | h4549
                                                      · linarith only [h4549, hlam, p4529_0]
                                                      · rcases p4529_3 (m.d 3 5) (by simp) with h4551 | h4551
                                                        · linarith only [h4116, h4551, hlam]
                                                        · linarith only [h4419, h4551, hlam]
                                                    · linarith only [h4416, h4548, hlam]
                                                  · linarith only [h4547, hlam, p4529_0]
                                                · linarith only [h4106, h4546, hlam]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p4529_1, u5ehi3]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4106, h4108, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4529_1, u5ehi4]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4116, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4529_1, u5ehi3]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                rcases p4529_3 (m.d 0 3) (by simp) with h4561 | h4561
                                                · linarith only [h4, h4561, hlam]
                                                · linarith only [h4106, h4561, hlam]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                rcases p4529_3 (m.d 0 3) (by simp) with h4564 | h4564
                                                · linarith only [h4, h4564, hlam]
                                                · linarith only [h4107, h4564, hlam]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4106, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4115, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4416, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4419, hlam, p4529_1]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4107, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4116, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h4417, hlam, p4529_0]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [h1, h4116, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4529_1]
                                              · have p4529_0 := h4529c.1
                                                have p4529_1 := h4529c.2.1
                                                have p4529_2 := h4529c.2.2.1
                                                have p4529_3 := h4529c.2.2.2
                                                linarith only [hlam, p4529_0]
                                            · linarith only [h4528, hlam, p4479_0]
                                          · linarith only [h3476, h4527, hlam]
                                        · linarith only [h4, h4526, hlam]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    rcases p4479_3 (m.d 0 2) (by simp) with h4580 | h4580
                                    · linarith only [h4023, h4580, hlam]
                                    · linarith only [h0, h4580, hlam]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4417, hlam, p4479_1]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [h4418, hlam, p4479_0]
                                  · have p4479_0 := h4479c.1
                                    have p4479_1 := h4479c.2.1
                                    have p4479_2 := h4479c.2.2.1
                                    have p4479_3 := h4479c.2.2.2
                                    linarith only [hlam, p4479_0]
                                · linarith only [h4023, h4478, hlam]
                              · linarith only [h3476, h4477, hlam]
                            · linarith only [h4, h4476, hlam]
                        · linarith only [h0, h4473, hlam]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4107, hlam, p4421_0]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [h4108, hlam, p4421_1]
                      · have p4421_0 := h4421c.1
                        have p4421_1 := h4421c.2.1
                        have p4421_2 := h4421c.2.2.1
                        have p4421_3 := h4421c.2.2.2
                        linarith only [hlam, p4421_0]
                  · linarith only [h3476, h4108, h4418, hlam]
                · linarith only [h0, h3476, h4, h4108, h4116, h4117, h4417, hc12, hc24, hlam, hphi]
              · linarith only [h4, h4106, h4416, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4596 | h4596
            · linarith only [h4, h4107, h4115, h4116, h4596, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4598 | h4598
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4599 | h4599
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4600 | h4600
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4601 | h4601
                    · linarith only [h4, h4107, h4115, h4116, h4596, h4601, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases h0bigk with h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c | h4603c
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        rcases p4603_3 (m.d 0 1) (by simp) with h4605 | h4605
                        · rcases p4603_3 (m.d 0 2) (by simp) with h4606 | h4606
                          · linarith only [h0, h4606, hlam]
                          · rcases p4603_3 (m.d 0 3) (by simp) with h4608 | h4608
                            · linarith only [h1, h4608, hlam]
                            · linarith only [h4, h4608, hlam]
                        · linarith only [h0, h4605, hlam]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4106, h4108, h4116, h4601, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4108, h4115, h4116, h4601, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4107, h4115, h4116, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h0, hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4, hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h3476, hlam, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4023, hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h1, hlam, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        rcases p4603_3 (m.d 0 1) (by simp) with h4621 | h4621
                        · rcases p4603_3 (m.d 0 2) (by simp) with h4622 | h4622
                          · linarith only [h4, h4622, hlam]
                          · rcases p4603_3 (m.d 0 3) (by simp) with h4624 | h4624
                            · rcases p4603_3 (m.d 0 4) (by simp) with h4625 | h4625
                              · linarith only [h4106, h4625, hlam]
                              · linarith only [h3476, h4625, hlam]
                            · linarith only [h4, h4624, hlam]
                        · linarith only [h0, h4621, hlam]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4108, h4115, h4116, h4601, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4, h4108, h4115, h4116, h4601, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h2, hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        rcases p4603_3 (m.d 0 1) (by simp) with h4634 | h4634
                        · rcases p4603_3 (m.d 0 2) (by simp) with h4635 | h4635
                          · linarith only [h3476, h4635, hlam]
                          · rcases p4603_3 (m.d 0 3) (by simp) with h4637 | h4637
                            · rcases p4603_3 (m.d 0 4) (by simp) with h4638 | h4638
                              · rcases p4603_3 (m.d 0 5) (by simp) with h4639 | h4639
                                · linarith only [h4108, h4639, hlam]
                                · linarith only [h4023, h4639, hlam]
                              · linarith only [h3476, h4638, hlam]
                            · linarith only [h4, h4637, hlam]
                        · linarith only [h0, h4634, hlam]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4106, hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4108, h4115, h4116, h4601, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h3, hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        rcases p4603_3 (m.d 0 1) (by simp) with h4649 | h4649
                        · rcases p4603_3 (m.d 0 2) (by simp) with h4650 | h4650
                          · linarith only [h4023, h4650, hlam]
                          · rcases p4603_3 (m.d 0 3) (by simp) with h4652 | h4652
                            · rcases p4603_3 (m.d 0 4) (by simp) with h4653 | h4653
                              · rcases p4603_3 (m.d 0 5) (by simp) with h4654 | h4654
                                · rcases h2bigk with h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c | h4655c
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4603_1, p4655_1]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h3476, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4023, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h0, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4109, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4111, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4113, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    rcases p4655_3 (m.d 0 2) (by simp) with h4666 | h4666
                                    · linarith only [h4666, hlam, p4655_0]
                                    · rcases p4655_3 (m.d 1 2) (by simp) with h4668 | h4668
                                      · linarith only [h4109, h4668, hlam]
                                      · rcases p4655_3 (m.d 2 3) (by simp) with h4670 | h4670
                                        · rcases p4655_3 (m.d 2 4) (by simp) with h4671 | h4671
                                          · linarith only [h4598, h4671, hlam]
                                          · linarith only [h3476, h4671, hlam]
                                        · linarith only [h4670, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    rcases p4655_3 (m.d 0 2) (by simp) with h4675 | h4675
                                    · linarith only [h4, h4675, hlam]
                                    · linarith only [h0, h4675, hlam]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h3476, h4108, h4115, h4116, h4601, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4655_1]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4023, hc02, hc23, hlam, hphi, p4655_1]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    rcases p4655_3 (m.d 0 2) (by simp) with h4681 | h4681
                                    · linarith only [h4681, hlam, p4655_0]
                                    · rcases p4655_3 (m.d 1 2) (by simp) with h4683 | h4683
                                      · linarith only [h4111, h4683, hlam]
                                      · rcases p4655_3 (m.d 2 3) (by simp) with h4685 | h4685
                                        · rcases p4655_3 (m.d 2 4) (by simp) with h4686 | h4686
                                          · rcases p4655_3 (m.d 2 5) (by simp) with h4687 | h4687
                                            · linarith only [h4600, h4687, hlam]
                                            · linarith only [h4023, h4687, hlam]
                                          · linarith only [h4686, hlam, p4655_0]
                                        · linarith only [h4, h4685, hlam]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    rcases p4655_3 (m.d 0 2) (by simp) with h4692 | h4692
                                    · linarith only [h3476, h4692, hlam]
                                    · linarith only [h0, h4692, hlam]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4598, hlam, p4655_1]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h0, h4023, hc12, hc24, hlam, hphi, p4603_1, p4655_1]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    rcases p4655_3 (m.d 0 2) (by simp) with h4698 | h4698
                                    · linarith only [h4698, hlam, p4655_0]
                                    · rcases p4655_3 (m.d 1 2) (by simp) with h4700 | h4700
                                      · linarith only [h4113, h4700, hlam]
                                      · rcases p4655_3 (m.d 2 3) (by simp) with h4702 | h4702
                                        · rcases p4655_3 (m.d 2 4) (by simp) with h4703 | h4703
                                          · rcases p4655_3 (m.d 2 5) (by simp) with h4704 | h4704
                                            · rcases h3bigk with h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c | h4705c
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                rcases p4705_3 (m.d 0 3) (by simp) with h4707 | h4707
                                                · rcases p4705_3 (m.d 1 3) (by simp) with h4708 | h4708
                                                  · linarith only [h1, h4708, hlam]
                                                  · rcases p4705_3 (m.d 2 3) (by simp) with h4710 | h4710
                                                    · rcases p4705_3 (m.d 3 4) (by simp) with h4711 | h4711
                                                      · linarith only [h4106, h4711, hlam]
                                                      · rcases p4705_3 (m.d 3 5) (by simp) with h4713 | h4713
                                                        · linarith only [h4107, h4713, hlam]
                                                        · linarith only [h4116, h4713, hlam]
                                                    · linarith only [h4109, h4710, hlam]
                                                · linarith only [h1, h4707, hlam]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4, hlam, p4705_1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4106, h4108, h4115, h4116, h4601, hlam, p4705_2]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4115, h4116, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4705_1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h1, hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4109, hlam, p4705_1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4108, h4116, h4601, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4705_1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4116, hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4106, h4108, h4116, h4601, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4705_1, u5ehi1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                rcases p4705_3 (m.d 0 3) (by simp) with h4727 | h4727
                                                · linarith only [h4, h4727, hlam]
                                                · linarith only [h1, h4727, hlam]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4, h4106, h4108, h4115, h4116, h4601, hlam, p4705_2]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4115, h4116, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4705_1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4106, hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4115, hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4598, hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4601, hlam, p4705_1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4107, hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4106, h4108, h4115, h4601, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4705_1]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [h4599, hlam, p4705_0]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                rcases p4705_3 (m.d 0 3) (by simp) with h4741 | h4741
                                                · rcases p4705_3 (m.d 1 3) (by simp) with h4742 | h4742
                                                  · linarith only [h4116, h4742, hlam]
                                                  · linarith only [h4115, h4742, hlam]
                                                · linarith only [h4106, h4741, hlam]
                                              · have p4705_0 := h4705c.1
                                                have p4705_1 := h4705c.2.1
                                                have p4705_2 := h4705c.2.2.1
                                                have p4705_3 := h4705c.2.2.2
                                                linarith only [hlam, p4705_0]
                                            · linarith only [h4704, hlam, p4655_0]
                                          · linarith only [h3476, h4703, hlam]
                                        · linarith only [h4, h4702, hlam]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    rcases p4655_3 (m.d 0 2) (by simp) with h4750 | h4750
                                    · linarith only [h4023, h4750, hlam]
                                    · linarith only [h0, h4750, hlam]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4599, hlam, p4655_1]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [h4600, hlam, p4655_0]
                                  · have p4655_0 := h4655c.1
                                    have p4655_1 := h4655c.2.1
                                    have p4655_2 := h4655c.2.2.1
                                    have p4655_3 := h4655c.2.2.2
                                    linarith only [hlam, p4655_0]
                                · linarith only [h4023, h4654, hlam]
                              · linarith only [h3476, h4653, hlam]
                            · linarith only [h4, h4652, hlam]
                        · linarith only [h0, h4649, hlam]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4107, hlam, p4603_0]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [h4108, hlam, p4603_1]
                      · have p4603_0 := h4603c.1
                        have p4603_1 := h4603c.2.1
                        have p4603_2 := h4603c.2.2.1
                        have p4603_3 := h4603c.2.2.2
                        linarith only [hlam, p4603_0]
                  · linarith only [h0, h3476, h4, h4106, h4108, h4600, hc12, hc23, hlam, hphi]
                · linarith only [h4, h4107, h4599, hlam]
              · linarith only [h4, h4107, h4115, h4116, h4598, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4766 | h4766
          · linarith only [h4106, h4115, h4766, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4768 | h4768
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4769 | h4769
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4770 | h4770
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4771 | h4771
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4772 | h4772
                    · rcases h0bigk with h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c | h4773c
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        rcases p4773_3 (m.d 0 1) (by simp) with h4775 | h4775
                        · rcases p4773_3 (m.d 0 2) (by simp) with h4776 | h4776
                          · linarith only [h0, h4776, hlam]
                          · rcases p4773_3 (m.d 0 3) (by simp) with h4778 | h4778
                            · linarith only [h1, h4778, hlam]
                            · linarith only [h4, h4778, hlam]
                        · linarith only [h0, h4775, hlam]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4106, h4115, h4768, hc01, hlam, hphi, ht0b, ht5b, p4773_1, u5ehi4]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4106, h4115, h4768, hc01, hlam, hphi, ht0b, ht5b, p4773_1, u5ehi4]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        rcases p4773_3 (m.d 0 1) (by simp) with h4784 | h4784
                        · rcases p4773_3 (m.d 0 2) (by simp) with h4785 | h4785
                          · linarith only [h0, h4785, hlam]
                          · rcases p4773_3 (m.d 0 3) (by simp) with h4787 | h4787
                            · linarith only [h1, h4787, hlam]
                            · linarith only [h4107, h4787, hlam]
                        · linarith only [h3, h4784, hlam]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h0, hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4, hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h3476, hlam, p4773_1]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4023, hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h1, hlam, p4773_1]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        rcases p4773_3 (m.d 0 1) (by simp) with h4797 | h4797
                        · rcases p4773_3 (m.d 0 2) (by simp) with h4798 | h4798
                          · linarith only [h4, h4798, hlam]
                          · rcases p4773_3 (m.d 0 3) (by simp) with h4800 | h4800
                            · rcases p4773_3 (m.d 0 4) (by simp) with h4801 | h4801
                              · linarith only [h4106, h4801, hlam]
                              · linarith only [h3476, h4801, hlam]
                            · linarith only [h4, h4800, hlam]
                        · linarith only [h0, h4797, hlam]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4106, h4115, h4768, hc03, hlam, hphi, ht0b, ht5b, p4773_1, u5ehi4]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4, h4107, h4109, h4766, hc12, hc23, hlam, hphi, p4773_1]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h2, hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        rcases p4773_3 (m.d 0 1) (by simp) with h4810 | h4810
                        · rcases p4773_3 (m.d 0 2) (by simp) with h4811 | h4811
                          · linarith only [h3476, h4811, hlam]
                          · rcases p4773_3 (m.d 0 3) (by simp) with h4813 | h4813
                            · rcases p4773_3 (m.d 0 4) (by simp) with h4814 | h4814
                              · rcases p4773_3 (m.d 0 5) (by simp) with h4815 | h4815
                                · linarith only [h4108, h4815, hlam]
                                · linarith only [h4023, h4815, hlam]
                              · linarith only [h3476, h4814, hlam]
                            · linarith only [h4, h4813, hlam]
                        · linarith only [h0, h4810, hlam]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4106, hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h3476, h4107, h4109, h4766, hc12, hc24, hlam, hphi, p4773_1]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h3, hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        rcases p4773_3 (m.d 0 1) (by simp) with h4825 | h4825
                        · rcases p4773_3 (m.d 0 2) (by simp) with h4826 | h4826
                          · linarith only [h4023, h4826, hlam]
                          · rcases p4773_3 (m.d 0 3) (by simp) with h4828 | h4828
                            · rcases p4773_3 (m.d 0 4) (by simp) with h4829 | h4829
                              · rcases p4773_3 (m.d 0 5) (by simp) with h4830 | h4830
                                · rcases h2bigk with h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c | h4831c
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4773_1, p4831_1]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h3476, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4023, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h0, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4109, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4111, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4113, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    rcases p4831_3 (m.d 0 2) (by simp) with h4842 | h4842
                                    · linarith only [h4842, hlam, p4831_0]
                                    · rcases p4831_3 (m.d 1 2) (by simp) with h4844 | h4844
                                      · linarith only [h4109, h4844, hlam]
                                      · rcases p4831_3 (m.d 2 3) (by simp) with h4846 | h4846
                                        · rcases p4831_3 (m.d 2 4) (by simp) with h4847 | h4847
                                          · linarith only [h4769, h4847, hlam]
                                          · linarith only [h3476, h4847, hlam]
                                        · linarith only [h4846, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    rcases p4831_3 (m.d 0 2) (by simp) with h4851 | h4851
                                    · linarith only [h4, h4851, hlam]
                                    · linarith only [h0, h4851, hlam]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h3476, hc02, hc23, hlam, hphi, p4831_1]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h0, h4023, hc12, hc23, hlam, hphi, p4831_1]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    rcases p4831_3 (m.d 0 2) (by simp) with h4857 | h4857
                                    · linarith only [h4857, hlam, p4831_0]
                                    · rcases p4831_3 (m.d 1 2) (by simp) with h4859 | h4859
                                      · linarith only [h4111, h4859, hlam]
                                      · rcases p4831_3 (m.d 2 3) (by simp) with h4861 | h4861
                                        · rcases p4831_3 (m.d 2 4) (by simp) with h4862 | h4862
                                          · rcases p4831_3 (m.d 2 5) (by simp) with h4863 | h4863
                                            · linarith only [h4771, h4863, hlam]
                                            · linarith only [h4023, h4863, hlam]
                                          · linarith only [h4862, hlam, p4831_0]
                                        · linarith only [h4, h4861, hlam]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    rcases p4831_3 (m.d 0 2) (by simp) with h4868 | h4868
                                    · linarith only [h3476, h4868, hlam]
                                    · linarith only [h0, h4868, hlam]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4769, hlam, p4831_1]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h0, h4023, hc12, hc24, hlam, hphi, p4773_1, p4831_1]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    rcases p4831_3 (m.d 0 2) (by simp) with h4874 | h4874
                                    · linarith only [h4874, hlam, p4831_0]
                                    · rcases p4831_3 (m.d 1 2) (by simp) with h4876 | h4876
                                      · linarith only [h4113, h4876, hlam]
                                      · rcases p4831_3 (m.d 2 3) (by simp) with h4878 | h4878
                                        · rcases p4831_3 (m.d 2 4) (by simp) with h4879 | h4879
                                          · rcases p4831_3 (m.d 2 5) (by simp) with h4880 | h4880
                                            · rcases h3bigk with h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c | h4881c
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                rcases p4881_3 (m.d 0 3) (by simp) with h4883 | h4883
                                                · rcases p4881_3 (m.d 1 3) (by simp) with h4884 | h4884
                                                  · linarith only [h1, h4884, hlam]
                                                  · rcases p4881_3 (m.d 2 3) (by simp) with h4886 | h4886
                                                    · rcases p4881_3 (m.d 3 4) (by simp) with h4887 | h4887
                                                      · linarith only [h4106, h4887, hlam]
                                                      · linarith only [h4115, h4887, hlam]
                                                    · linarith only [h4109, h4886, hlam]
                                                · linarith only [h1, h4883, hlam]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4, hlam, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4, h4109, h4766, h4772, hc12, hc23, hlam, hphi, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4, h4109, h4766, hc12, hc23, hlam, hphi, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h1, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4109, hlam, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4115, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4766, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4106, h4109, h4766, h4772, hc12, hc23, hlam, hphi, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                rcases p4881_3 (m.d 0 3) (by simp) with h4901 | h4901
                                                · linarith only [h4, h4901, hlam]
                                                · linarith only [h1, h4901, hlam]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4115, h4768, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4881_1, u5ehi4]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4109, h4766, hc12, hc23, hlam, hphi, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4106, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4, h4106, h4109, hc12, hc23, hlam, hphi, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4769, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4, h4106, h4109, h4766, hc12, hc23, hlam, hphi, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4107, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4, h4107, h4109, hc12, hc23, hlam, hphi, p4881_1]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4770, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [h4772, hlam, p4881_0]
                                              · have p4881_0 := h4881c.1
                                                have p4881_1 := h4881c.2.1
                                                have p4881_2 := h4881c.2.2.1
                                                have p4881_3 := h4881c.2.2.2
                                                linarith only [hlam, p4881_0]
                                            · linarith only [h4880, hlam, p4831_0]
                                          · linarith only [h3476, h4879, hlam]
                                        · linarith only [h4, h4878, hlam]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    rcases p4831_3 (m.d 0 2) (by simp) with h4920 | h4920
                                    · linarith only [h4023, h4920, hlam]
                                    · linarith only [h0, h4920, hlam]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4770, hlam, p4831_1]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [h4771, hlam, p4831_0]
                                  · have p4831_0 := h4831c.1
                                    have p4831_1 := h4831c.2.1
                                    have p4831_2 := h4831c.2.2.1
                                    have p4831_3 := h4831c.2.2.2
                                    linarith only [hlam, p4831_0]
                                · linarith only [h4023, h4830, hlam]
                              · linarith only [h3476, h4829, hlam]
                            · linarith only [h4, h4828, hlam]
                        · linarith only [h0, h4825, hlam]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4107, hlam, p4773_0]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [h4108, hlam, p4773_1]
                      · have p4773_0 := h4773c.1
                        have p4773_1 := h4773c.2.1
                        have p4773_2 := h4773c.2.2.1
                        have p4773_3 := h4773c.2.2.2
                        linarith only [hlam, p4773_0]
                    · linarith only [h2, h4109, h4115, h4768, h4772, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h3476, h4, h4106, h4115, h4768, h4771, hc12, hc23, hlam, hphi]
                · linarith only [h4, h4023, h4106, h4107, h4115, h4768, h4770, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h4, h4106, h4769, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4937 | h4937
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4938 | h4938
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4939 | h4939
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4940 | h4940
                    · linarith only [h4, h4106, h4111, h4768, h4940, hc12, hc23, hlam, hphi]
                    · linarith only [h4, h4106, h4108, h4109, h4115, h4940, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h3476, h4, h4106, h4108, h4939, hc12, hc23, hlam, hphi]
                · linarith only [h4, h4107, h4938, hlam]
              · linarith only [h4, h4106, h4937, hlam]

end R2N4
