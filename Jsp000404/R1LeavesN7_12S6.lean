import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4101 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4172 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4173 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h4174 | h4174
  · linarith only [h0, h4, h4174, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4176 | h4176
    · linarith only [h0, h3686, h4176, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4178 | h4178
      · linarith only [h0, h4101, h4178, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4180 | h4180
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4181 | h4181
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4182 | h4182
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4183 | h4183
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4184 | h4184
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4185 | h4185
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4186 | h4186
                    · linarith only [h1, h4180, h4186, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases h1bigk with h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        rcases p4188_3 (m.d 0 1) (by simp) with h4190 | h4190
                        · rcases p4188_3 (m.d 1 2) (by simp) with h4191 | h4191
                          · linarith only [h4191, hlam, p4188_0]
                          · rcases p4188_3 (m.d 1 3) (by simp) with h4193 | h4193
                            · linarith only [h1, h4193, hlam]
                            · linarith only [h4174, h4193, hlam]
                        · linarith only [h4190, hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h4180, h4182, h4186, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h4182, h4186, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        rcases p4188_3 (m.d 0 1) (by simp) with h4199 | h4199
                        · rcases p4188_3 (m.d 1 2) (by simp) with h4200 | h4200
                          · linarith only [h0, h4200, hlam]
                          · rcases p4188_3 (m.d 1 3) (by simp) with h4202 | h4202
                            · linarith only [h1, h4202, hlam]
                            · linarith only [h4181, h4202, hlam]
                        · linarith only [h4199, hlam, p4188_0]
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
                        linarith only [h4174, hlam, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h4176, hlam, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h4178, hlam, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h1, hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        rcases p4188_3 (m.d 0 1) (by simp) with h4212 | h4212
                        · rcases p4188_3 (m.d 1 2) (by simp) with h4213 | h4213
                          · linarith only [h4174, h4213, hlam]
                          · rcases p4188_3 (m.d 1 3) (by simp) with h4215 | h4215
                            · rcases p4188_3 (m.d 1 4) (by simp) with h4216 | h4216
                              · linarith only [h4180, h4216, hlam]
                              · linarith only [h4176, h4216, hlam]
                            · linarith only [h4174, h4215, hlam]
                        · linarith only [h0, h4212, hlam]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h1, h4182, h4186, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h1, h4182, h4186, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h2, hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        rcases p4188_3 (m.d 0 1) (by simp) with h4225 | h4225
                        · rcases p4188_3 (m.d 1 2) (by simp) with h4226 | h4226
                          · linarith only [h4176, h4226, hlam]
                          · rcases p4188_3 (m.d 1 3) (by simp) with h4228 | h4228
                            · rcases p4188_3 (m.d 1 4) (by simp) with h4229 | h4229
                              · rcases p4188_3 (m.d 1 5) (by simp) with h4230 | h4230
                                · linarith only [h4182, h4230, hlam]
                                · linarith only [h4178, h4230, hlam]
                              · linarith only [h4176, h4229, hlam]
                            · linarith only [h4174, h4228, hlam]
                        · linarith only [h0, h4225, hlam]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h4180, hlam, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h2, h4182, h4186, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4188_1]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h3, hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        rcases p4188_3 (m.d 0 1) (by simp) with h4240 | h4240
                        · rcases p4188_3 (m.d 1 2) (by simp) with h4241 | h4241
                          · linarith only [h4178, h4241, hlam]
                          · rcases p4188_3 (m.d 1 3) (by simp) with h4243 | h4243
                            · rcases p4188_3 (m.d 1 4) (by simp) with h4244 | h4244
                              · rcases p4188_3 (m.d 1 5) (by simp) with h4245 | h4245
                                · rcases h2bigk with h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4101, h4183, h4185, hc12, hc23, hlam, hphi, p4246_1]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h3686, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4101, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h0, hlam, p4246_1]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4174, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4176, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4178, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    rcases p4246_3 (m.d 0 2) (by simp) with h4257 | h4257
                                    · linarith only [h4257, hlam, p4246_0]
                                    · rcases p4246_3 (m.d 1 2) (by simp) with h4259 | h4259
                                      · linarith only [h4174, h4259, hlam]
                                      · rcases p4246_3 (m.d 2 3) (by simp) with h4261 | h4261
                                        · rcases p4246_3 (m.d 2 4) (by simp) with h4262 | h4262
                                          · linarith only [h4183, h4262, hlam]
                                          · linarith only [h3686, h4262, hlam]
                                        · linarith only [h4261, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    rcases p4246_3 (m.d 0 2) (by simp) with h4266 | h4266
                                    · linarith only [h4, h4266, hlam]
                                    · linarith only [h0, h4266, hlam]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h3686, hc02, hc23, hlam, hphi, p4246_1]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h0, h4101, hc12, hc23, hlam, hphi, p4246_1]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    rcases p4246_3 (m.d 0 2) (by simp) with h4272 | h4272
                                    · linarith only [h4272, hlam, p4246_0]
                                    · rcases p4246_3 (m.d 1 2) (by simp) with h4274 | h4274
                                      · linarith only [h4176, h4274, hlam]
                                      · rcases p4246_3 (m.d 2 3) (by simp) with h4276 | h4276
                                        · rcases p4246_3 (m.d 2 4) (by simp) with h4277 | h4277
                                          · rcases p4246_3 (m.d 2 5) (by simp) with h4278 | h4278
                                            · linarith only [h4185, h4278, hlam]
                                            · linarith only [h4101, h4278, hlam]
                                          · linarith only [h4277, hlam, p4246_0]
                                        · linarith only [h4, h4276, hlam]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    rcases p4246_3 (m.d 0 2) (by simp) with h4283 | h4283
                                    · linarith only [h3686, h4283, hlam]
                                    · linarith only [h0, h4283, hlam]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4183, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h3, h4101, hc12, hc24, hlam, hphi, p4188_1, p4246_1]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    rcases p4246_3 (m.d 0 2) (by simp) with h4289 | h4289
                                    · linarith only [h4289, hlam, p4246_0]
                                    · rcases p4246_3 (m.d 1 2) (by simp) with h4291 | h4291
                                      · linarith only [h4178, h4291, hlam]
                                      · rcases p4246_3 (m.d 2 3) (by simp) with h4293 | h4293
                                        · rcases p4246_3 (m.d 2 4) (by simp) with h4294 | h4294
                                          · rcases p4246_3 (m.d 2 5) (by simp) with h4295 | h4295
                                            · rcases h4bigk with h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c | h4296c
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4182, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4188_1, p4296_1]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h3686, hlam, p4296_1]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                rcases p4296_3 (m.d 0 4) (by simp) with h4300 | h4300
                                                · rcases p4296_3 (m.d 1 4) (by simp) with h4301 | h4301
                                                  · linarith only [h2, h4301, hlam]
                                                  · linarith only [h4180, h4301, hlam]
                                                · linarith only [h4172, h4300, hlam]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                rcases p4296_3 (m.d 0 4) (by simp) with h4305 | h4305
                                                · rcases p4296_3 (m.d 1 4) (by simp) with h4306 | h4306
                                                  · linarith only [h2, h4306, hlam]
                                                  · linarith only [h4182, h4306, hlam]
                                                · linarith only [h4305, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h2, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4176, hlam, p4296_1]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                rcases p4296_3 (m.d 0 4) (by simp) with h4313 | h4313
                                                · rcases p4296_3 (m.d 1 4) (by simp) with h4314 | h4314
                                                  · rcases p4296_3 (m.d 2 4) (by simp) with h4315 | h4315
                                                    · rcases p4296_3 (m.d 3 4) (by simp) with h4316 | h4316
                                                      · linarith only [h4180, h4316, hlam]
                                                      · rcases p4296_3 (m.d 4 5) (by simp) with h4318 | h4318
                                                        · linarith only [h4182, h4318, hlam]
                                                        · linarith only [h4186, h4318, hlam]
                                                    · linarith only [h4183, h4315, hlam]
                                                  · linarith only [h4180, h4314, hlam]
                                                · linarith only [h4172, h4313, hlam]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h1, h4180, h4186, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4296_1]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4173, h4183, h4186, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4296_1]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4182, h4183, h4186, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4296_1]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                rcases p4296_3 (m.d 0 4) (by simp) with h4328 | h4328
                                                · linarith only [h3686, h4328, hlam]
                                                · linarith only [h4172, h4328, hlam]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                rcases p4296_3 (m.d 0 4) (by simp) with h4331 | h4331
                                                · linarith only [h3686, h4331, hlam]
                                                · linarith only [h4173, h4331, hlam]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4172, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4180, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4183, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4186, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4173, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4182, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h4185, hlam, p4296_0]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [h1, h4180, h4182, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4296_1]
                                              · have p4296_0 := h4296c.1
                                                have p4296_1 := h4296c.2.1
                                                have p4296_2 := h4296c.2.2.1
                                                have p4296_3 := h4296c.2.2.2
                                                linarith only [hlam, p4296_0]
                                            · linarith only [h4295, hlam, p4246_0]
                                          · linarith only [h3686, h4294, hlam]
                                        · linarith only [h4, h4293, hlam]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    rcases p4246_3 (m.d 0 2) (by simp) with h4347 | h4347
                                    · linarith only [h4101, h4347, hlam]
                                    · linarith only [h0, h4347, hlam]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4184, hlam, p4246_0]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [h4185, hlam, p4246_1]
                                  · have p4246_0 := h4246c.1
                                    have p4246_1 := h4246c.2.1
                                    have p4246_2 := h4246c.2.2.1
                                    have p4246_3 := h4246c.2.2.2
                                    linarith only [hlam, p4246_0]
                                · linarith only [h4178, h4245, hlam]
                              · linarith only [h4176, h4244, hlam]
                            · linarith only [h4174, h4243, hlam]
                        · linarith only [h0, h4240, hlam]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h4181, hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [h4182, hlam, p4188_0]
                      · have p4188_0 := h4188c.1
                        have p4188_1 := h4188c.2.1
                        have p4188_2 := h4188c.2.2.1
                        have p4188_3 := h4188c.2.2.2
                        linarith only [hlam, p4188_0]
                  · linarith only [h0, h1, h3686, h4180, h4182, h4185, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1, h4, h4181, h4184, hlam]
              · linarith only [h4, h4172, h4183, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4363 | h4363
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4364 | h4364
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4365 | h4365
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4366 | h4366
                    · linarith only [h4180, h4182, h4366, hlam]
                    · rcases h1bigk with h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c | h4368c
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        rcases p4368_3 (m.d 0 1) (by simp) with h4370 | h4370
                        · rcases p4368_3 (m.d 1 2) (by simp) with h4371 | h4371
                          · linarith only [h4371, hlam, p4368_0]
                          · rcases p4368_3 (m.d 1 3) (by simp) with h4373 | h4373
                            · linarith only [h1, h4373, hlam]
                            · linarith only [h4174, h4373, hlam]
                        · linarith only [h4370, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4181, hc01, hlam, hphi, ht0b, ht5b, p4368_1, u5ehi3]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        rcases p4368_3 (m.d 0 1) (by simp) with h4378 | h4378
                        · rcases p4368_3 (m.d 1 2) (by simp) with h4379 | h4379
                          · linarith only [h0, h4379, hlam]
                          · rcases p4368_3 (m.d 1 3) (by simp) with h4381 | h4381
                            · linarith only [h1, h4381, hlam]
                            · linarith only [h4180, h4381, hlam]
                        · linarith only [h4378, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        rcases p4368_3 (m.d 0 1) (by simp) with h4385 | h4385
                        · rcases p4368_3 (m.d 1 2) (by simp) with h4386 | h4386
                          · linarith only [h0, h4386, hlam]
                          · rcases p4368_3 (m.d 1 3) (by simp) with h4388 | h4388
                            · linarith only [h1, h4388, hlam]
                            · linarith only [h4181, h4388, hlam]
                        · linarith only [h4385, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h0, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4174, hlam, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4176, hlam, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4178, hlam, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h1, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        rcases p4368_3 (m.d 0 1) (by simp) with h4398 | h4398
                        · rcases p4368_3 (m.d 1 2) (by simp) with h4399 | h4399
                          · linarith only [h4174, h4399, hlam]
                          · rcases p4368_3 (m.d 1 3) (by simp) with h4401 | h4401
                            · rcases p4368_3 (m.d 1 4) (by simp) with h4402 | h4402
                              · linarith only [h4180, h4402, hlam]
                              · linarith only [h4176, h4402, hlam]
                            · linarith only [h4174, h4401, hlam]
                        · linarith only [h0, h4398, hlam]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        rcases p4368_3 (m.d 0 1) (by simp) with h4408 | h4408
                        · rcases p4368_3 (m.d 1 2) (by simp) with h4409 | h4409
                          · linarith only [h4174, h4409, hlam]
                          · rcases p4368_3 (m.d 1 3) (by simp) with h4411 | h4411
                            · rcases p4368_3 (m.d 1 4) (by simp) with h4412 | h4412
                              · linarith only [h4180, h4412, hlam]
                              · rcases p4368_3 (m.d 1 5) (by simp) with h4414 | h4414
                                · linarith only [h4181, h4414, hlam]
                                · linarith only [h4182, h4414, hlam]
                            · linarith only [h4180, h4411, hlam]
                        · linarith only [h2, h4408, hlam]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h1, h4181, hc01, hlam, hphi, ht0b, ht5b, p4368_1, u5ehi3]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h2, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4172, h4173, h4182, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4180, hlam, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4182, hlam, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h3, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4, h4172, h4173, h4182, hc12, hc23, hlam, hphi, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4181, hlam, p4368_0]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [h4, h4172, h4173, h4176, h4182, hc12, hc23, hlam, hphi, p4368_1]
                      · have p4368_0 := h4368c.1
                        have p4368_1 := h4368c.2.1
                        have p4368_2 := h4368c.2.2.1
                        have p4368_3 := h4368c.2.2.2
                        linarith only [hlam, p4368_0]
                  · linarith only [h3686, h4173, h4365, hlam]
                · linarith only [h1, h4, h4181, h4364, hlam]
              · linarith only [h4, h4172, h4173, h4180, h4182, h4363, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4433 | h4433
            · linarith only [h4180, h4181, h4433, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4435 | h4435
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4436 | h4436
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4437 | h4437
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4438 | h4438
                    · linarith only [h4180, h4181, h4433, h4436, h4438, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases h1bigk with h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c | h4440c
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        rcases p4440_3 (m.d 0 1) (by simp) with h4442 | h4442
                        · rcases p4440_3 (m.d 1 2) (by simp) with h4443 | h4443
                          · linarith only [h4443, hlam, p4440_0]
                          · rcases p4440_3 (m.d 1 3) (by simp) with h4445 | h4445
                            · linarith only [h1, h4445, hlam]
                            · linarith only [h4174, h4445, hlam]
                        · linarith only [h4442, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        rcases p4440_3 (m.d 0 1) (by simp) with h4449 | h4449
                        · rcases p4440_3 (m.d 1 2) (by simp) with h4450 | h4450
                          · linarith only [h0, h4450, hlam]
                          · rcases p4440_3 (m.d 1 3) (by simp) with h4452 | h4452
                            · linarith only [h4452, hlam, p4440_0]
                            · rcases p4440_3 (m.d 1 4) (by simp) with h4454 | h4454
                              · linarith only [h2, h4454, hlam]
                              · rcases p4440_3 (m.d 1 5) (by simp) with h4456 | h4456
                                · linarith only [h3, h4456, hlam]
                                · linarith only [h4181, h4456, hlam]
                        · linarith only [h4449, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        rcases p4440_3 (m.d 0 1) (by simp) with h4460 | h4460
                        · rcases p4440_3 (m.d 1 2) (by simp) with h4461 | h4461
                          · linarith only [h0, h4461, hlam]
                          · rcases p4440_3 (m.d 1 3) (by simp) with h4463 | h4463
                            · linarith only [h1, h4463, hlam]
                            · linarith only [h4180, h4463, hlam]
                        · linarith only [h4460, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        rcases p4440_3 (m.d 0 1) (by simp) with h4467 | h4467
                        · rcases p4440_3 (m.d 1 2) (by simp) with h4468 | h4468
                          · linarith only [h0, h4468, hlam]
                          · rcases p4440_3 (m.d 1 3) (by simp) with h4470 | h4470
                            · linarith only [h1, h4470, hlam]
                            · rcases p4440_3 (m.d 1 4) (by simp) with h4472 | h4472
                              · linarith only [h2, h4472, hlam]
                              · rcases p4440_3 (m.d 1 5) (by simp) with h4474 | h4474
                                · linarith only [h4474, hlam, p4440_0]
                                · rcases h2bigk with h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c | h4476c
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4, hc12, hc23, hlam, hphi, p4476_1]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h3686, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4101, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h0, hlam, p4476_1]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4174, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4176, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4178, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    rcases p4476_3 (m.d 0 2) (by simp) with h4487 | h4487
                                    · linarith only [h4487, hlam, p4476_0]
                                    · rcases p4476_3 (m.d 1 2) (by simp) with h4489 | h4489
                                      · linarith only [h4174, h4489, hlam]
                                      · rcases p4476_3 (m.d 2 3) (by simp) with h4491 | h4491
                                        · rcases p4476_3 (m.d 2 4) (by simp) with h4492 | h4492
                                          · linarith only [h4435, h4492, hlam]
                                          · linarith only [h3686, h4492, hlam]
                                        · linarith only [h4491, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    rcases p4476_3 (m.d 0 2) (by simp) with h4496 | h4496
                                    · linarith only [h4, h4496, hlam]
                                    · linarith only [h0, h4496, hlam]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h3686, h4173, h4181, h4438, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4476_1]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4101, hc02, hc23, hlam, hphi, p4476_1]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    rcases p4476_3 (m.d 0 2) (by simp) with h4502 | h4502
                                    · linarith only [h4502, hlam, p4476_0]
                                    · rcases p4476_3 (m.d 1 2) (by simp) with h4504 | h4504
                                      · linarith only [h4176, h4504, hlam]
                                      · rcases p4476_3 (m.d 2 3) (by simp) with h4506 | h4506
                                        · rcases p4476_3 (m.d 2 4) (by simp) with h4507 | h4507
                                          · rcases p4476_3 (m.d 2 5) (by simp) with h4508 | h4508
                                            · linarith only [h4437, h4508, hlam]
                                            · linarith only [h4101, h4508, hlam]
                                          · linarith only [h4507, hlam, p4476_0]
                                        · linarith only [h4, h4506, hlam]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    rcases p4476_3 (m.d 0 2) (by simp) with h4513 | h4513
                                    · linarith only [h3686, h4513, hlam]
                                    · linarith only [h0, h4513, hlam]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4435, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4101, h4173, h4180, h4181, h4438, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4476_1]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    rcases p4476_3 (m.d 0 2) (by simp) with h4519 | h4519
                                    · linarith only [h4519, hlam, p4476_0]
                                    · rcases p4476_3 (m.d 1 2) (by simp) with h4521 | h4521
                                      · linarith only [h4178, h4521, hlam]
                                      · rcases p4476_3 (m.d 2 3) (by simp) with h4523 | h4523
                                        · rcases p4476_3 (m.d 2 4) (by simp) with h4524 | h4524
                                          · rcases p4476_3 (m.d 2 5) (by simp) with h4525 | h4525
                                            · rcases h4bigk with h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c | h4526c
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                rcases p4526_3 (m.d 0 4) (by simp) with h4528 | h4528
                                                · rcases p4526_3 (m.d 1 4) (by simp) with h4529 | h4529
                                                  · linarith only [h2, h4529, hlam]
                                                  · rcases p4526_3 (m.d 2 4) (by simp) with h4531 | h4531
                                                    · rcases p4526_3 (m.d 3 4) (by simp) with h4532 | h4532
                                                      · linarith only [h4172, h4532, hlam]
                                                      · rcases p4526_3 (m.d 4 5) (by simp) with h4534 | h4534
                                                        · linarith only [h4173, h4534, hlam]
                                                        · linarith only [h4433, h4534, hlam]
                                                    · linarith only [h4176, h4531, hlam]
                                                · linarith only [h2, h4528, hlam]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h3686, hlam, p4526_1]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4173, h4180, h4181, h4438, hlam, p4526_2]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4180, h4181, h4438, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4526_1]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h2, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4176, hlam, p4526_1]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4180, h4181, h4438, hc34, hc45, hlam, hphi, p4526_1]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4433, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4173, h4435, h4438, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4526_1, u5ehi3]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                rcases p4526_3 (m.d 0 4) (by simp) with h4548 | h4548
                                                · linarith only [h3686, h4548, hlam]
                                                · linarith only [h2, h4548, hlam]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h3686, h4173, h4180, h4181, h4438, hlam, p4526_2]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4180, h4181, h4438, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4526_1]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4172, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4180, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4435, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4438, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4173, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h3686, h4173, h4176, hc12, hc24, hlam, hphi, p4526_1]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [h4437, hlam, p4526_0]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                rcases p4526_3 (m.d 0 4) (by simp) with h4562 | h4562
                                                · rcases p4526_3 (m.d 1 4) (by simp) with h4563 | h4563
                                                  · linarith only [h4433, h4563, hlam]
                                                  · linarith only [h4180, h4563, hlam]
                                                · linarith only [h4172, h4562, hlam]
                                              · have p4526_0 := h4526c.1
                                                have p4526_1 := h4526c.2.1
                                                have p4526_2 := h4526c.2.2.1
                                                have p4526_3 := h4526c.2.2.2
                                                linarith only [hlam, p4526_0]
                                            · linarith only [h4525, hlam, p4476_0]
                                          · linarith only [h3686, h4524, hlam]
                                        · linarith only [h4, h4523, hlam]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    rcases p4476_3 (m.d 0 2) (by simp) with h4571 | h4571
                                    · linarith only [h4101, h4571, hlam]
                                    · linarith only [h0, h4571, hlam]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4436, hlam, p4476_0]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [h4437, hlam, p4476_1]
                                  · have p4476_0 := h4476c.1
                                    have p4476_1 := h4476c.2.1
                                    have p4476_2 := h4476c.2.2.1
                                    have p4476_3 := h4476c.2.2.2
                                    linarith only [hlam, p4476_0]
                        · linarith only [h4467, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h0, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4174, hlam, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4176, hlam, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4178, hlam, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h1, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4181, hc12, hc35, hlam, hphi, ht23, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4176, h4181, hc12, hc35, hlam, hphi, ht23, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4181, hlam, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h2, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4180, h4181, hc12, hc35, hlam, hphi, ht23, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4180, hlam, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4433, hlam, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h3, hlam, p4440_0]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4, h4172, h4173, h4433, hc12, hc23, hlam, hphi, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h3, h4180, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [h4, h4172, h4173, h4176, h4433, hc12, hc23, hlam, hphi, p4440_1]
                      · have p4440_0 := h4440c.1
                        have p4440_1 := h4440c.2.1
                        have p4440_2 := h4440c.2.2.1
                        have p4440_3 := h4440c.2.2.2
                        linarith only [hlam, p4440_0]
                  · linarith only [h0, h3686, h4, h4172, h4173, h4437, hc12, hc23, hlam, hphi]
                · linarith only [h4, h4172, h4173, h4176, h4433, h4436, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h4, h4172, h4173, h4176, h4180, h4433, h4435, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4601 | h4601
          · linarith only [h4172, h4180, h4601, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4603 | h4603
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4604 | h4604
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4605 | h4605
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4606 | h4606
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4607 | h4607
                    · rcases h1bigk with h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c | h4608c
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        rcases p4608_3 (m.d 0 1) (by simp) with h4610 | h4610
                        · rcases p4608_3 (m.d 1 2) (by simp) with h4611 | h4611
                          · linarith only [h4611, hlam, p4608_0]
                          · rcases p4608_3 (m.d 1 3) (by simp) with h4613 | h4613
                            · linarith only [h1, h4613, hlam]
                            · linarith only [h4174, h4613, hlam]
                        · linarith only [h4610, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        rcases p4608_3 (m.d 0 1) (by simp) with h4617 | h4617
                        · rcases p4608_3 (m.d 1 2) (by simp) with h4618 | h4618
                          · linarith only [h0, h4618, hlam]
                          · rcases p4608_3 (m.d 1 3) (by simp) with h4620 | h4620
                            · linarith only [h4620, hlam, p4608_0]
                            · rcases p4608_3 (m.d 1 4) (by simp) with h4622 | h4622
                              · linarith only [h2, h4622, hlam]
                              · linarith only [h4180, h4622, hlam]
                        · linarith only [h4617, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4603, hc01, hlam, hphi, ht0b, ht5b, p4608_1, u5ehi4]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        rcases p4608_3 (m.d 0 1) (by simp) with h4627 | h4627
                        · rcases p4608_3 (m.d 1 2) (by simp) with h4628 | h4628
                          · linarith only [h0, h4628, hlam]
                          · rcases p4608_3 (m.d 1 3) (by simp) with h4630 | h4630
                            · linarith only [h1, h4630, hlam]
                            · rcases p4608_3 (m.d 1 4) (by simp) with h4632 | h4632
                              · linarith only [h2, h4632, hlam]
                              · linarith only [h4603, h4632, hlam]
                        · linarith only [h4627, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h0, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4174, hlam, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4176, hlam, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4178, hlam, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h1, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4601, h4605, hc12, hc25, hlam, hphi, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4180, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4601, hlam, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h2, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4, h4172, h4180, hc12, hc23, hlam, hphi, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4, h4172, h4174, h4180, hc12, hc23, hlam, hphi, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4, h4172, h4180, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4608_1, u5ehi1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h3, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4, h4172, h4180, h4603, hc12, hc23, hlam, hphi, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4, h4172, h4174, h4180, h4603, hc12, hc23, hlam, hphi, p4608_1]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [h4603, hlam, p4608_0]
                      · have p4608_0 := h4608c.1
                        have p4608_1 := h4608c.2.1
                        have p4608_2 := h4608c.2.2.1
                        have p4608_3 := h4608c.2.2.2
                        linarith only [hlam, p4608_0]
                    · linarith only [h3686, h4173, h4174, h4180, h4604, h4607, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h3686, h4603, h4606, hlam]
                · linarith only [h4, h4172, h4180, h4603, h4605, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
              · linarith only [h4, h4172, h4604, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4660 | h4660
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4661 | h4661
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4662 | h4662
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4663 | h4663
                    · linarith only [h4, h4172, h4174, h4180, h4603, h4663, hc12, hc23, hlam, hphi]
                    · linarith only [h3686, h4173, h4174, h4180, h4663, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h3686, h4, h4172, h4173, h4662, hc12, hc23, hlam, hphi]
                · linarith only [h4, h4172, h4174, h4180, h4661, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h4, h4172, h4660, hlam]

end R2N4
