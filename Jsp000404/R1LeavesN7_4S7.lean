import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8736000 in
set_option maxHeartbeats 8736000 in
theorem r1l7_11_23_L_I_H_I_s6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_11_23_L_I_H_I_s7 m hb1 hb3 h0 h1 h2 h3 h4 h5 h6 h7
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4155 | h4155
    · linarith only [h4155, h6, h7, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4157 | h4157
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4158 | h4158
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4159 | h4159
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4160 | h4160
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4161 | h4161
              · linarith only [h1, h4161, h7, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4163 | h4163
                · linarith only [h2, h4155, h4163, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4165 | h4165
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4166 | h4166
                    · linarith only [h1, h4157, h4166, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4168 | h4168
                      · linarith only [h4155, h4168, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4170 | h4170
                        · linarith only [h4155, h4159, h4165, h4166, h4170, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h1bigk with h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h4159, h4165, h4166, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            rcases p4172_3 (m.d 0 1) (by simp) with h4175 | h4175
                            · rcases p4172_3 (m.d 1 2) (by simp) with h4176 | h4176
                              · linarith only [h0, h4176, hlam]
                              · linarith only [h4157, h4176, hlam]
                            · linarith only [h4175, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            rcases p4172_3 (m.d 0 1) (by simp) with h4180 | h4180
                            · rcases p4172_3 (m.d 1 2) (by simp) with h4181 | h4181
                              · linarith only [h0, h4181, hlam]
                              · linarith only [h4158, h4181, hlam]
                            · linarith only [h4180, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            rcases p4172_3 (m.d 0 1) (by simp) with h4185 | h4185
                            · rcases p4172_3 (m.d 1 2) (by simp) with h4186 | h4186
                              · linarith only [h0, h4186, hlam]
                              · linarith only [h4159, h4186, hlam]
                            · linarith only [h4185, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h0, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h0, h4157, h4165, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            rcases p4172_3 (m.d 0 1) (by simp) with h4193 | h4193
                            · rcases p4172_3 (m.d 1 2) (by simp) with h4194 | h4194
                              · rcases p4172_3 (m.d 1 3) (by simp) with h4195 | h4195
                                · linarith only [h4157, h4195, hlam]
                                · linarith only [h4160, h4195, hlam]
                              · linarith only [h4158, h4194, hlam]
                            · linarith only [h2, h4193, hlam]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h0, h4157, h4161, h4165, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h1, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h4157, hlam, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h1, h4158, h4165, h4170, h7, hc34, hc45, hlam, hphi, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h4161, hlam, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h2, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h4158, hlam, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h4160, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h4163, hlam, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h3, hlam, p4172_0]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h4159, hlam, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [h3, h4157, h4165, h4170, h7, hc34, hc45, hlam, hphi, p4172_1]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            rcases p4172_3 (m.d 0 1) (by simp) with h4214 | h4214
                            · rcases p4172_3 (m.d 1 2) (by simp) with h4215 | h4215
                              · rcases p4172_3 (m.d 1 3) (by simp) with h4216 | h4216
                                · linarith only [h4161, h4216, hlam]
                                · linarith only [h4160, h4216, hlam]
                              · linarith only [h4158, h4215, hlam]
                            · linarith only [h2, h4214, hlam]
                          · have p4172_0 := h4172c.1
                            have p4172_1 := h4172c.2.1
                            have p4172_2 := h4172c.2.2.1
                            have p4172_3 := h4172c.2.2.2
                            linarith only [hlam, p4172_0]
                  · linarith only [h4165, h6, h7, hc23, hc35, hlam, hphi]
            · linarith only [h4157, h4160, h6, h7, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4224 | h4224
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4225 | h4225
              · linarith only [h1, h4225, h7, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4227 | h4227
                · linarith only [h2, h4155, h4227, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4229 | h4229
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4230 | h4230
                    · linarith only [h4157, h4159, h4230, h7, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4232 | h4232
                      · linarith only [h2, h3, h4155, h4157, h4158, h4159, h4229, h4232, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h4157, h4159, h4229, h4232, hc34, hc45, hlam, hphi]
                  · linarith only [h4229, h6, h7, hc23, hc35, hlam, hphi]
            · linarith only [h4224, h6, h7, hc13, hc35, hlam, hphi]
        · linarith only [h4155, h4157, h4158, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4238 | h4238
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4239 | h4239
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4240 | h4240
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4241 | h4241
              · linarith only [h4, h4157, h4238, h4241, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h4157, h4239, h4241, hlam]
            · linarith only [h4157, h4238, h4240, h6, h7, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4245 | h4245
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4246 | h4246
              · linarith only [h1, h4246, h7, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4248 | h4248
                · linarith only [h4, h4155, h4157, h4238, h4248, h7, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4250 | h4250
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4251 | h4251
                    · linarith only [h4, h4251, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4253 | h4253
                      · linarith only [h2, h4155, h4238, h4253, h6, h7, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4255 | h4255
                        · linarith only [h4, h4155, h4157, h4238, h4250, h4255, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h4, h4157, h4238, h4255, h7, hc24, hc45, hlam, hphi]
                  · linarith only [h4157, h4238, h4250, h6, h7, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h4245, h6, h7, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4260 | h4260
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4261 | h4261
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4262 | h4262
              · linarith only [h1, h4262, h7, hlam]
              · linarith only [h4157, h4260, h4262, hlam]
            · linarith only [h4157, h4261, h6, h7, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4266 | h4266
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4267 | h4267
              · linarith only [h1, h4267, h7, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4269 | h4269
                · linarith only [h2, h4155, h4238, h4269, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4271 | h4271
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4272 | h4272
                    · linarith only [h4, h4272, h7, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4274 | h4274
                      · linarith only [h4155, h4274, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4276 | h4276
                        · linarith only [h4155, h4238, h4276, h5, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c | h4278c
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            rcases p4278_3 (m.d 0 1) (by simp) with h4280 | h4280
                            · rcases p4278_3 (m.d 1 2) (by simp) with h4281 | h4281
                              · linarith only [h4281, hlam, p4278_0]
                              · rcases p4278_3 (m.d 1 3) (by simp) with h4283 | h4283
                                · linarith only [h1, h4283, hlam]
                                · linarith only [h4157, h4283, hlam]
                            · linarith only [h4280, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            rcases p4278_3 (m.d 0 1) (by simp) with h4287 | h4287
                            · rcases p4278_3 (m.d 1 2) (by simp) with h4288 | h4288
                              · linarith only [h0, h4288, hlam]
                              · rcases p4278_3 (m.d 1 3) (by simp) with h4290 | h4290
                                · linarith only [h4290, hlam, p4278_0]
                                · rcases p4278_3 (m.d 1 4) (by simp) with h4292 | h4292
                                  · linarith only [h2, h4292, hlam]
                                  · rcases p4278_3 (m.d 1 5) (by simp) with h4294 | h4294
                                    · linarith only [h3, h4294, hlam]
                                    · linarith only [h4267, h4294, hlam]
                            · linarith only [h4287, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            rcases p4278_3 (m.d 0 1) (by simp) with h4298 | h4298
                            · rcases p4278_3 (m.d 1 2) (by simp) with h4299 | h4299
                              · linarith only [h0, h4299, hlam]
                              · rcases p4278_3 (m.d 1 3) (by simp) with h4301 | h4301
                                · linarith only [h1, h4301, hlam]
                                · linarith only [h4266, h4301, hlam]
                            · linarith only [h4298, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            rcases p4278_3 (m.d 0 1) (by simp) with h4305 | h4305
                            · rcases p4278_3 (m.d 1 2) (by simp) with h4306 | h4306
                              · linarith only [h0, h4306, hlam]
                              · rcases p4278_3 (m.d 1 3) (by simp) with h4308 | h4308
                                · linarith only [h1, h4308, hlam]
                                · rcases p4278_3 (m.d 1 4) (by simp) with h4310 | h4310
                                  · linarith only [h2, h4310, hlam]
                                  · rcases p4278_3 (m.d 1 5) (by simp) with h4312 | h4312
                                    · linarith only [h4312, hlam, p4278_0]
                                    · rcases h3bigk with h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c | h4314c
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4266, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h7, hc23, hc35, hlam, hphi, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4276, h7, hc34, hc45, hlam, hphi, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h7, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h1, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4157, hlam, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4267, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4278_1, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4267, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4, h4276, h7, hc34, hc45, hlam, hphi, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4272, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h6, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4266, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4271, hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [hlam, p4314_0]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4276, hlam, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4276, hc03, hc45, hlam, hphi, ht34, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4266, h4276, hc34, hc45, hlam, hphi, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4238, h4271, h4276, hc12, hc45, hlam, hphi, ht23, ht34, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [h4276, hc34, hc45, hlam, hphi, p4314_1]
                                      · have p4314_0 := h4314c.1
                                        have p4314_1 := h4314c.2.1
                                        have p4314_2 := h4314c.2.2.1
                                        have p4314_3 := h4314c.2.2.2
                                        linarith only [hlam, p4314_0]
                            · linarith only [h4305, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h0, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h4157, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h4238, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h4260, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h1, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h1, h4276, h7, hc12, hc45, hlam, hphi, ht23, ht34, p4278_1]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h4, h4157, h4276, h7, hc14, hc45, hlam, hphi, p4278_1]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h4267, hlam, p4278_1]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h2, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h2, h4276, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34, p4278_1]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h4266, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h4269, hlam, p4278_1]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h3, hlam, p4278_0]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            rcases p4278_3 (m.d 0 1) (by simp) with h4357 | h4357
                            · rcases p4278_3 (m.d 1 2) (by simp) with h4358 | h4358
                              · linarith only [h4260, h4358, hlam]
                              · rcases p4278_3 (m.d 1 3) (by simp) with h4360 | h4360
                                · linarith only [h4267, h4360, hlam]
                                · linarith only [h4157, h4360, hlam]
                            · linarith only [h0, h4357, hlam]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [h3, h4266, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4278_1]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            rcases p4278_3 (m.d 0 1) (by simp) with h4365 | h4365
                            · rcases p4278_3 (m.d 1 2) (by simp) with h4366 | h4366
                              · linarith only [h4260, h4366, hlam]
                              · rcases p4278_3 (m.d 1 3) (by simp) with h4368 | h4368
                                · linarith only [h4267, h4368, hlam]
                                · linarith only [h4266, h4368, hlam]
                            · linarith only [h2, h4365, hlam]
                          · have p4278_0 := h4278c.1
                            have p4278_1 := h4278c.2.1
                            have p4278_2 := h4278c.2.2.1
                            have p4278_3 := h4278c.2.2.2
                            linarith only [hlam, p4278_0]
                  · linarith only [h1, h4266, h4271, h7, hc23, hc35, hlam, hphi]
            · linarith only [h4266, h6, h7, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  exact r1l7_11_23_L_I_H_I_s6 m hb1 hb3 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4375 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 4 5 (by decide) (by decide) with h4376 | h4376
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4377 | h4377
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4378 | h4378
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4379 | h4379
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4380 | h4380
          · linarith only [h1, h4380, h6, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4382 | h4382
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4383 | h4383
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4384 | h4384
                · linarith only [h1, h4377, h4384, h6, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4386 | h4386
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4387 | h4387
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4388 | h4388
                      · rcases h1bigk with h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c | h4389c
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h4378, h4384, h4386, hc01, hc35, hlam, hphi, ht0b, ht5b, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          rcases p4389_3 (m.d 0 1) (by simp) with h4392 | h4392
                          · rcases p4389_3 (m.d 1 2) (by simp) with h4393 | h4393
                            · linarith only [h0, h4393, hlam]
                            · linarith only [h4377, h4393, hlam]
                          · linarith only [h4392, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          rcases p4389_3 (m.d 0 1) (by simp) with h4397 | h4397
                          · rcases p4389_3 (m.d 1 2) (by simp) with h4398 | h4398
                            · linarith only [h0, h4398, hlam]
                            · linarith only [h4378, h4398, hlam]
                          · linarith only [h4397, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          rcases p4389_3 (m.d 0 1) (by simp) with h4402 | h4402
                          · rcases p4389_3 (m.d 1 2) (by simp) with h4403 | h4403
                            · linarith only [h0, h4403, hlam]
                            · linarith only [h4379, h4403, hlam]
                          · linarith only [h4402, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h0, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h0, h4377, h4386, h4388, hc01, hc45, hlam, hphi, ht0b, ht5b, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h0, h4377, h4380, h4386, h4388, hc01, hc45, hlam, hphi, ht0b, ht5b, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          rcases p4389_3 (m.d 0 1) (by simp) with h4411 | h4411
                          · rcases p4389_3 (m.d 1 2) (by simp) with h4412 | h4412
                            · rcases p4389_3 (m.d 1 3) (by simp) with h4413 | h4413
                              · linarith only [h4377, h4413, hlam]
                              · linarith only [h4382, h4413, hlam]
                            · linarith only [h4379, h4412, hlam]
                          · linarith only [h3, h4411, hlam]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h1, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h4377, hlam, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h4380, hlam, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          rcases p4389_3 (m.d 0 1) (by simp) with h4422 | h4422
                          · rcases p4389_3 (m.d 1 2) (by simp) with h4423 | h4423
                            · rcases p4389_3 (m.d 1 3) (by simp) with h4424 | h4424
                              · rcases p4389_3 (m.d 1 4) (by simp) with h4425 | h4425
                                · rcases p4389_3 (m.d 1 5) (by simp) with h4426 | h4426
                                  · linarith only [h4382, h4426, hlam]
                                  · rcases h3bigk with h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c | h4428c
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4379, h4386, h4388, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4389_1, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4386, h4388, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h6, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4388, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h1, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4386, h4388, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4380, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h1, h4388, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4377, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4384, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h0, h4, h4388, hc01, hc45, hlam, hphi, ht0b, ht5b, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4377, hc23, hc34, hlam, hphi, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [hc23, hc34, hlam, hphi, p4428_1]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      rcases p4428_3 (m.d 0 3) (by simp) with h4448 | h4448
                                      · linarith only [h4448, h6, hlam]
                                      · linarith only [h4375, h4448, hlam]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4375, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4382, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4386, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [h4388, hlam, p4428_0]
                                    · have p4428_0 := h4428c.1
                                      have p4428_1 := h4428c.2.1
                                      have p4428_2 := h4428c.2.2.1
                                      have p4428_3 := h4428c.2.2.2
                                      linarith only [hlam, p4428_0]
                                · linarith only [h4383, h4425, hlam]
                              · linarith only [h4382, h4424, hlam]
                            · linarith only [h4379, h4423, hlam]
                          · linarith only [h3, h4422, hlam]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h2, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h4378, hlam, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h0, h4377, h4378, h4386, h4388, hc01, hc45, hlam, hphi, ht0b, ht5b, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          rcases p4389_3 (m.d 0 1) (by simp) with h4464 | h4464
                          · rcases p4389_3 (m.d 1 2) (by simp) with h4465 | h4465
                            · rcases p4389_3 (m.d 1 3) (by simp) with h4466 | h4466
                              · linarith only [h4380, h4466, hlam]
                              · linarith only [h4382, h4466, hlam]
                            · linarith only [h4379, h4465, hlam]
                          · linarith only [h3, h4464, hlam]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h3, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h4379, hlam, p4389_1]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h4382, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [h4383, hlam, p4389_0]
                        · have p4389_0 := h4389c.1
                          have p4389_1 := h4389c.2.1
                          have p4389_2 := h4389c.2.2.1
                          have p4389_3 := h4389c.2.2.2
                          linarith only [hlam, p4389_0]
                      · linarith only [h4376, h4388, h6, hlam]
                    · linarith only [h0, h4378, h4383, h4384, h4386, h4387, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4375, h4386, h6, hc23, hc34, hlam, hphi]
              · linarith only [h4380, h4382, h4383, hlam]
            · linarith only [h4375, h4382, h6, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4481 | h4481
          · linarith only [h1, h4375, h4481, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4483 | h4483
            · linarith only [h4377, h4379, h4483, hlam]
            · linarith only [h4375, h4483, h6, hc13, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4486 | h4486
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4487 | h4487
          · linarith only [h1, h4375, h4487, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4489 | h4489
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4490 | h4490
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4491 | h4491
                · linarith only [h4377, h4378, h4491, h5, h6, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4493 | h4493
                  · linarith only [h4377, h4378, h4493, h5, hc02, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h4489, h4493, h6, hc23, hc34, hlam, hphi]
              · linarith only [h4375, h4376, h4377, h4378, h4490, h6, hc23, hc34, hlam, hphi]
            · linarith only [h4375, h4489, h6, hc13, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4498 | h4498
          · linarith only [h1, h4375, h4498, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4500 | h4500
            · linarith only [h4377, h4486, h4500, hlam]
            · linarith only [h4375, h4500, h6, hc13, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4503 | h4503
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4504 | h4504
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4505 | h4505
          · linarith only [h4, h4377, h4505, h6, hlam]
          · linarith only [h4377, h4503, h4505, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4508 | h4508
          · linarith only [h4, h4377, h4503, h4508, h6, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h4377, h4503, h4508, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4511 | h4511
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4512 | h4512
          · linarith only [h1, h4375, h4512, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4514 | h4514
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4515 | h4515
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4516 | h4516
                · linarith only [h4, h4516, h6, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4518 | h4518
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4519 | h4519
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4520 | h4520
                      · rcases h1bigk with h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c | h4521c
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          rcases p4521_3 (m.d 0 1) (by simp) with h4523 | h4523
                          · rcases p4521_3 (m.d 1 2) (by simp) with h4524 | h4524
                            · linarith only [h4524, hlam, p4521_0]
                            · rcases p4521_3 (m.d 1 3) (by simp) with h4526 | h4526
                              · linarith only [h1, h4526, hlam]
                              · linarith only [h4377, h4526, hlam]
                          · linarith only [h4523, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          rcases p4521_3 (m.d 0 1) (by simp) with h4530 | h4530
                          · rcases p4521_3 (m.d 1 2) (by simp) with h4531 | h4531
                            · linarith only [h0, h4531, hlam]
                            · rcases p4521_3 (m.d 1 3) (by simp) with h4533 | h4533
                              · linarith only [h4533, hlam, p4521_0]
                              · rcases p4521_3 (m.d 1 4) (by simp) with h4535 | h4535
                                · linarith only [h2, h4535, hlam]
                                · linarith only [h4512, h4535, hlam]
                          · linarith only [h4530, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          rcases p4521_3 (m.d 0 1) (by simp) with h4539 | h4539
                          · rcases p4521_3 (m.d 1 2) (by simp) with h4540 | h4540
                            · linarith only [h0, h4540, hlam]
                            · rcases p4521_3 (m.d 1 3) (by simp) with h4542 | h4542
                              · linarith only [h1, h4542, hlam]
                              · rcases p4521_3 (m.d 1 4) (by simp) with h4544 | h4544
                                · linarith only [h4544, hlam, p4521_0]
                                · rcases p4521_3 (m.d 1 5) (by simp) with h4546 | h4546
                                  · linarith only [h3, h4546, hlam]
                                  · rcases h3bigk with h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c | h4548c
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4377, h4511, h4518, h4520, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4377, h4511, h4518, h4520, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h6, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4520, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h1, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4377, hlam, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4512, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h1, h4520, hc01, hc45, hlam, hphi, ht0b, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4516, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4, h4520, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4377, h4511, h4518, h4520, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4377, h4511, h4518, h4520, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4548_1]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      rcases p4548_3 (m.d 0 3) (by simp) with h4568 | h4568
                                      · linarith only [h4568, h6, hlam]
                                      · linarith only [h4375, h4568, hlam]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4375, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4514, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4518, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [h4520, hlam, p4548_0]
                                    · have p4548_0 := h4548c.1
                                      have p4548_1 := h4548c.2.1
                                      have p4548_2 := h4548c.2.2.1
                                      have p4548_3 := h4548c.2.2.2
                                      linarith only [hlam, p4548_0]
                          · linarith only [h4539, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          rcases p4521_3 (m.d 0 1) (by simp) with h4577 | h4577
                          · rcases p4521_3 (m.d 1 2) (by simp) with h4578 | h4578
                            · linarith only [h0, h4578, hlam]
                            · linarith only [h4511, h4578, hlam]
                          · linarith only [h4577, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h0, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h4377, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h4503, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h0, h4, h4377, hc01, hc15, hlam, hphi, ht0b, ht5b, p4521_1]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h1, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h1, h6, hc12, hc34, hlam, hphi, ht23, p4521_1]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h4512, hlam, p4521_1]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          rcases p4521_3 (m.d 0 1) (by simp) with h4591 | h4591
                          · rcases p4521_3 (m.d 1 2) (by simp) with h4592 | h4592
                            · linarith only [h4377, h4592, hlam]
                            · linarith only [h4511, h4592, hlam]
                          · linarith only [h3, h4591, hlam]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h2, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h0, h4503, h4511, h4518, h4520, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4521_1]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h0, h4377, h4503, h4511, h4518, h4520, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4521_1]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          rcases p4521_3 (m.d 0 1) (by simp) with h4600 | h4600
                          · rcases p4521_3 (m.d 1 2) (by simp) with h4601 | h4601
                            · linarith only [h4503, h4601, hlam]
                            · linarith only [h4511, h4601, hlam]
                          · linarith only [h3, h4600, hlam]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h3, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h4511, hlam, p4521_1]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h4514, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [h4515, hlam, p4521_0]
                        · have p4521_0 := h4521c.1
                          have p4521_1 := h4521c.2.1
                          have p4521_2 := h4521c.2.2.1
                          have p4521_3 := h4521c.2.2.2
                          linarith only [hlam, p4521_0]
                      · linarith only [h1, h4376, h4377, h4511, h4520, h6, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4377, h4511, h4515, h4516, h4519, hlam]
                  · linarith only [h4375, h4377, h4511, h4518, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h4377, h4511, h4512, h4515, hlam]
            · linarith only [h4375, h4377, h4511, h4514, h6, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4615 | h4615
          · linarith only [h1, h4375, h4615, h6, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4617 | h4617
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4618 | h4618
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4619 | h4619
                · linarith only [h4, h4619, h6, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4621 | h4621
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4622 | h4622
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4623 | h4623
                      · rcases h1bigk with h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c | h4624c
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4626 | h4626
                          · rcases p4624_3 (m.d 1 2) (by simp) with h4627 | h4627
                            · linarith only [h4627, hlam, p4624_0]
                            · rcases p4624_3 (m.d 1 3) (by simp) with h4629 | h4629
                              · linarith only [h1, h4629, hlam]
                              · linarith only [h4377, h4629, hlam]
                          · linarith only [h4626, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4633 | h4633
                          · rcases p4624_3 (m.d 1 2) (by simp) with h4634 | h4634
                            · linarith only [h0, h4634, hlam]
                            · rcases p4624_3 (m.d 1 3) (by simp) with h4636 | h4636
                              · linarith only [h4636, hlam, p4624_0]
                              · rcases p4624_3 (m.d 1 4) (by simp) with h4638 | h4638
                                · linarith only [h2, h4638, hlam]
                                · linarith only [h4615, h4638, hlam]
                          · linarith only [h4633, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4642 | h4642
                          · rcases p4624_3 (m.d 1 2) (by simp) with h4643 | h4643
                            · linarith only [h0, h4643, hlam]
                            · rcases p4624_3 (m.d 1 3) (by simp) with h4645 | h4645
                              · linarith only [h1, h4645, hlam]
                              · rcases p4624_3 (m.d 1 4) (by simp) with h4647 | h4647
                                · linarith only [h4647, hlam, p4624_0]
                                · rcases p4624_3 (m.d 1 5) (by simp) with h4649 | h4649
                                  · linarith only [h3, h4649, hlam]
                                  · rcases h3bigk with h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c | h4651c
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4511, h4617, h6, hc12, hc34, hlam, hphi, ht23, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h6, hc23, hc34, hlam, hphi, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h6, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4623, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h1, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4377, hlam, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4615, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4615, h4623, hc01, hc45, hlam, hphi, ht0b, ht5b, p4624_1, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4619, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4, h4623, h6, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [hc03, hc34, hlam, hphi, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4617, h4623, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4511, h4621, hc12, hc34, hlam, hphi, ht23, p4651_1]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      rcases p4651_3 (m.d 0 3) (by simp) with h4671 | h4671
                                      · linarith only [h4671, h6, hlam]
                                      · linarith only [h4375, h4671, hlam]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4375, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4617, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4621, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [h4623, hlam, p4651_0]
                                    · have p4651_0 := h4651c.1
                                      have p4651_1 := h4651c.2.1
                                      have p4651_2 := h4651c.2.2.1
                                      have p4651_3 := h4651c.2.2.2
                                      linarith only [hlam, p4651_0]
                          · linarith only [h4642, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4680 | h4680
                          · rcases p4624_3 (m.d 1 2) (by simp) with h4681 | h4681
                            · linarith only [h0, h4681, hlam]
                            · rcases p4624_3 (m.d 1 3) (by simp) with h4683 | h4683
                              · linarith only [h1, h4683, hlam]
                              · linarith only [h4617, h4683, hlam]
                          · linarith only [h4680, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h0, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4377, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4503, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4511, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h1, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h1, h6, hc12, hc34, hlam, hphi, ht23, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4615, hlam, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h1, h4511, h6, hc12, hc34, hlam, hphi, ht23, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h2, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4698 | h4698
                          · rcases p4624_3 (m.d 1 2) (by simp) with h4699 | h4699
                            · linarith only [h4503, h4699, hlam]
                            · rcases p4624_3 (m.d 1 3) (by simp) with h4701 | h4701
                              · linarith only [h4615, h4701, hlam]
                              · linarith only [h4377, h4701, hlam]
                          · linarith only [h0, h4698, hlam]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h0, h4503, h4617, h4623, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          rcases p4624_3 (m.d 0 1) (by simp) with h4707 | h4707
                          · rcases p4624_3 (m.d 1 2) (by simp) with h4708 | h4708
                            · linarith only [h4503, h4708, hlam]
                            · rcases p4624_3 (m.d 1 3) (by simp) with h4710 | h4710
                              · linarith only [h4615, h4710, hlam]
                              · linarith only [h4617, h4710, hlam]
                          · linarith only [h3, h4707, hlam]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h3, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h3, h4375, h6, hc12, hc34, hlam, hphi, ht23, p4624_1]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4617, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [h4618, hlam, p4624_0]
                        · have p4624_0 := h4624c.1
                          have p4624_1 := h4624c.2.1
                          have p4624_2 := h4624c.2.2.1
                          have p4624_3 := h4624c.2.2.2
                          linarith only [hlam, p4624_0]
                      · linarith only [h4376, h4623, h6, hlam]
                    · linarith only [h4, h4377, h4503, h4617, h4618, h4622, h6, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h4375, h4377, h4621, h6, hc13, hc34, hlam, hphi]
              · linarith only [h4615, h4617, h4618, hlam]
            · linarith only [h4375, h4377, h4617, h6, hc12, hc34, hlam, hphi, ht23]
  · linarith only [h4375, h4376, h6, hlam]

end R2N4
