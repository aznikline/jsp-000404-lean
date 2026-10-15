import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h15538 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h16013 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h16176 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h15532 := hg15532
  rcases m.htr 1 2 3 (by decide) (by decide) with h16177 | h16177
  · rcases m.htr 1 2 4 (by decide) (by decide) with h16178 | h16178
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16179 | h16179
      · rcases m.htr 1 3 4 (by decide) (by decide) with h16180 | h16180
        · linarith only [h0, h15532, h15538, h16180, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h16182 | h16182
          · linarith only [h15532, h16013, h16182, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16184 | h16184
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16185 | h16185
              · linarith only [h15535, h15538, h16185, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16187 | h16187
                · linarith only [h15532, h16013, h16177, h16187, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16189 | h16189
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16190 | h16190
                    · rcases h0bigk with h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c | h16191c
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [hlam, p16191_0]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h0, hlam, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16194 | h16194
                        · rcases p16191_3 (m.d 0 2) (by simp) with h16195 | h16195
                          · rcases p16191_3 (m.d 0 3) (by simp) with h16196 | h16196
                            · linarith only [h15532, h16196, hlam]
                            · rcases p16191_3 (m.d 0 4) (by simp) with h16198 | h16198
                              · linarith only [h15533, h16198, hlam]
                              · linarith only [h15538, h16198, hlam]
                          · linarith only [h15535, h16195, hlam]
                        · linarith only [h15532, h16194, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h0, h15536, h16189, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16204 | h16204
                        · rcases p16191_3 (m.d 0 2) (by simp) with h16205 | h16205
                          · rcases p16191_3 (m.d 0 3) (by simp) with h16206 | h16206
                            · linarith only [h15532, h16206, hlam]
                            · rcases p16191_3 (m.d 0 4) (by simp) with h16208 | h16208
                              · linarith only [h15533, h16208, hlam]
                              · linarith only [h16176, h16208, hlam]
                          · linarith only [h15537, h16205, hlam]
                        · linarith only [h15534, h16204, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h0, h15533, h16178, h16189, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [hlam, p16191_0]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16215 | h16215
                        · linarith only [h0, h16215, hlam]
                        · linarith only [h15532, h16215, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16218 | h16218
                        · linarith only [h0, h16218, hlam]
                        · linarith only [h15533, h16218, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16221 | h16221
                        · linarith only [h0, h16221, hlam]
                        · linarith only [h15534, h16221, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h15532, hlam, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h15535, hlam, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [hlam, p16191_0]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h15538, hlam, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h16013, hlam, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h15533, hlam, p16191_0]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h15536, hlam, p16191_0]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16231 | h16231
                        · rcases p16191_3 (m.d 0 2) (by simp) with h16232 | h16232
                          · rcases p16191_3 (m.d 0 3) (by simp) with h16233 | h16233
                            · linarith only [h15538, h16233, hlam]
                            · rcases p16191_3 (m.d 0 4) (by simp) with h16235 | h16235
                              · rcases p16191_3 (m.d 0 5) (by simp) with h16236 | h16236
                                · linarith only [h16176, h16236, hlam]
                                · linarith only [h16013, h16236, hlam]
                              · linarith only [h15538, h16235, hlam]
                          · linarith only [h15535, h16232, hlam]
                        · linarith only [h15532, h16231, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [hlam, p16191_0]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16243 | h16243
                        · rcases p16191_3 (m.d 0 2) (by simp) with h16244 | h16244
                          · rcases p16191_3 (m.d 0 3) (by simp) with h16245 | h16245
                            · linarith only [h15538, h16245, hlam]
                            · rcases p16191_3 (m.d 0 4) (by simp) with h16247 | h16247
                              · rcases p16191_3 (m.d 0 5) (by simp) with h16248 | h16248
                                · linarith only [h16176, h16248, hlam]
                                · rcases h2bigk with h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c | h16250c
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h0, hlam, p16250_1]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    rcases p16250_3 (m.d 0 2) (by simp) with h16253 | h16253
                                    · rcases p16250_3 (m.d 1 2) (by simp) with h16254 | h16254
                                      · rcases p16250_3 (m.d 2 3) (by simp) with h16255 | h16255
                                        · linarith only [h16255, hlam, p16250_0]
                                        · rcases p16250_3 (m.d 2 4) (by simp) with h16257 | h16257
                                          · linarith only [h15536, h16257, hlam]
                                          · linarith only [h16185, h16257, hlam]
                                      · linarith only [h16177, h16254, hlam]
                                    · linarith only [h16253, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    rcases p16250_3 (m.d 0 2) (by simp) with h16262 | h16262
                                    · rcases p16250_3 (m.d 1 2) (by simp) with h16263 | h16263
                                      · rcases p16250_3 (m.d 2 3) (by simp) with h16264 | h16264
                                        · linarith only [h15535, h16264, hlam]
                                        · rcases p16250_3 (m.d 2 4) (by simp) with h16266 | h16266
                                          · linarith only [h16266, hlam, p16250_0]
                                          · rcases p16250_3 (m.d 2 5) (by simp) with h16268 | h16268
                                            · linarith only [h15537, h16268, hlam]
                                            · rcases h3bigk with h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c | h16270c
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h15533, h16013, h16177, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16191_1, p16270_1]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h0, h15533, h16013, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16191_1, p16270_1]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h15538, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16013, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h15532, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h0, h15532, h15533, h16013, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16191_1, p16270_1]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16180, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16182, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h15535, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16177, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16185, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16187, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                rcases p16270_3 (m.d 0 3) (by simp) with h16286 | h16286
                                                · linarith only [h16286, hlam, p16270_0]
                                                · rcases p16270_3 (m.d 1 3) (by simp) with h16288 | h16288
                                                  · linarith only [h16180, h16288, hlam]
                                                  · rcases p16270_3 (m.d 2 3) (by simp) with h16290 | h16290
                                                    · linarith only [h16185, h16290, hlam]
                                                    · rcases p16270_3 (m.d 3 4) (by simp) with h16292 | h16292
                                                      · rcases p16270_3 (m.d 3 5) (by simp) with h16293 | h16293
                                                        · linarith only [h16190, h16293, hlam]
                                                        · linarith only [h16013, h16293, hlam]
                                                      · linarith only [h16292, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                rcases p16270_3 (m.d 0 3) (by simp) with h16297 | h16297
                                                · linarith only [h15538, h16297, hlam]
                                                · linarith only [h15532, h16297, hlam]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                rcases p16270_3 (m.d 0 3) (by simp) with h16300 | h16300
                                                · linarith only [h15538, h16300, hlam]
                                                · linarith only [h15535, h16300, hlam]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16013, hc03, hc34, hlam, hphi, p16270_1]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                rcases p16270_3 (m.d 0 3) (by simp) with h16305 | h16305
                                                · linarith only [h16305, hlam, p16270_0]
                                                · rcases p16270_3 (m.d 1 3) (by simp) with h16307 | h16307
                                                  · linarith only [h16182, h16307, hlam]
                                                  · rcases p16270_3 (m.d 2 3) (by simp) with h16309 | h16309
                                                    · linarith only [h16187, h16309, hlam]
                                                    · rcases p16270_3 (m.d 3 4) (by simp) with h16311 | h16311
                                                      · rcases p16270_3 (m.d 3 5) (by simp) with h16312 | h16312
                                                        · rcases h5bigk with h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c | h16313c
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h0, h15533, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p16191_1, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h0, h15533, h16187, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16191_1, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16013, hlam, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h0, h15533, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16191_1, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h15534, hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h0, h15534, h16187, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16182, hlam, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h0, h15533, h15534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16191_1, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h15537, hlam, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16179, hlam, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16187, hlam, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h15537, hc02, hc45, hlam, hphi, ht0b, ht5b, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h15532, h16013, h16177, hc23, hc35, hlam, hphi, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16177, h16182, hc23, hc35, hlam, hphi, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16187, hc23, hc35, hlam, hphi, p16313_1]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            rcases p16313_3 (m.d 0 5) (by simp) with h16333 | h16333
                                                            · linarith only [h16013, h16333, hlam]
                                                            · linarith only [h16176, h16333, hlam]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16176, hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16184, hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16189, hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [h16190, hlam, p16313_0]
                                                          · have p16313_0 := h16313c.1
                                                            have p16313_1 := h16313c.2.1
                                                            have p16313_2 := h16313c.2.2.1
                                                            have p16313_3 := h16313c.2.2.2
                                                            linarith only [hlam, p16313_0]
                                                        · linarith only [h16312, hlam, p16270_0]
                                                      · linarith only [h15538, h16311, hlam]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                rcases p16270_3 (m.d 0 3) (by simp) with h16343 | h16343
                                                · linarith only [h16013, h16343, hlam]
                                                · linarith only [h15532, h16343, hlam]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                rcases p16270_3 (m.d 0 3) (by simp) with h16346 | h16346
                                                · linarith only [h16013, h16346, hlam]
                                                · linarith only [h15535, h16346, hlam]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [h16190, hlam, p16270_0]
                                              · have p16270_0 := h16270c.1
                                                have p16270_1 := h16270c.2.1
                                                have p16270_2 := h16270c.2.2.1
                                                have p16270_3 := h16270c.2.2.2
                                                linarith only [hlam, p16270_0]
                                      · linarith only [h16178, h16263, hlam]
                                    · linarith only [h16262, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    rcases p16250_3 (m.d 0 2) (by simp) with h16353 | h16353
                                    · rcases p16250_3 (m.d 1 2) (by simp) with h16354 | h16354
                                      · rcases p16250_3 (m.d 2 3) (by simp) with h16355 | h16355
                                        · linarith only [h15535, h16355, hlam]
                                        · rcases p16250_3 (m.d 2 4) (by simp) with h16357 | h16357
                                          · linarith only [h15536, h16357, hlam]
                                          · linarith only [h16189, h16357, hlam]
                                      · linarith only [h16179, h16354, hlam]
                                    · linarith only [h16353, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h0, h15533, h16178, h16189, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16250_1]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h0, h15532, h15533, h16013, h16177, hlam, p16191_1, p16250_2]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    rcases p16250_3 (m.d 0 2) (by simp) with h16365 | h16365
                                    · linarith only [h0, h16365, hlam]
                                    · linarith only [h15536, h16365, hlam]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h0, h15533, h15537, hlam, p16191_1, p16250_2]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h15535, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h16177, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h16185, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h16187, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h15536, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h16178, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h0, h15533, h16178, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16250_1]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h0, h15533, h16178, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16250_1]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h15537, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h16179, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h15537, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16191_1, p16250_1]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [h16189, hlam, p16250_0]
                                  · have p16250_0 := h16250c.1
                                    have p16250_1 := h16250c.2.1
                                    have p16250_2 := h16250c.2.2.1
                                    have p16250_3 := h16250c.2.2.2
                                    linarith only [hlam, p16250_0]
                              · linarith only [h16176, h16247, hlam]
                          · linarith only [h15537, h16244, hlam]
                        · linarith only [h15534, h16243, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h15534, hlam, p16191_0]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h15537, hlam, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        rcases p16191_3 (m.d 0 1) (by simp) with h16389 | h16389
                        · rcases p16191_3 (m.d 0 2) (by simp) with h16390 | h16390
                          · rcases p16191_3 (m.d 0 3) (by simp) with h16391 | h16391
                            · linarith only [h16013, h16391, hlam]
                            · rcases p16191_3 (m.d 0 4) (by simp) with h16393 | h16393
                              · rcases p16191_3 (m.d 0 5) (by simp) with h16394 | h16394
                                · rcases h2bigk with h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c | h16395c
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h0, hlam, p16395_1]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    rcases p16395_3 (m.d 0 2) (by simp) with h16398 | h16398
                                    · rcases p16395_3 (m.d 1 2) (by simp) with h16399 | h16399
                                      · rcases p16395_3 (m.d 2 3) (by simp) with h16400 | h16400
                                        · linarith only [h16400, hlam, p16395_0]
                                        · rcases p16395_3 (m.d 2 4) (by simp) with h16402 | h16402
                                          · linarith only [h15536, h16402, hlam]
                                          · linarith only [h16185, h16402, hlam]
                                      · linarith only [h16177, h16399, hlam]
                                    · linarith only [h16398, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    rcases p16395_3 (m.d 0 2) (by simp) with h16407 | h16407
                                    · rcases p16395_3 (m.d 1 2) (by simp) with h16408 | h16408
                                      · rcases p16395_3 (m.d 2 3) (by simp) with h16409 | h16409
                                        · linarith only [h15535, h16409, hlam]
                                        · rcases p16395_3 (m.d 2 4) (by simp) with h16411 | h16411
                                          · linarith only [h16411, hlam, p16395_0]
                                          · rcases p16395_3 (m.d 2 5) (by simp) with h16413 | h16413
                                            · linarith only [h15537, h16413, hlam]
                                            · rcases h3bigk with h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c | h16415c
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16177, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16191_1, p16415_1]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h0, h15534, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16191_1, p16415_1]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h15538, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16013, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h15532, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h0, h15532, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16415_1]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16180, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16182, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h15535, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16177, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16185, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16187, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                rcases p16415_3 (m.d 0 3) (by simp) with h16431 | h16431
                                                · linarith only [h16431, hlam, p16415_0]
                                                · rcases p16415_3 (m.d 1 3) (by simp) with h16433 | h16433
                                                  · linarith only [h16180, h16433, hlam]
                                                  · rcases p16415_3 (m.d 2 3) (by simp) with h16435 | h16435
                                                    · linarith only [h16185, h16435, hlam]
                                                    · rcases p16415_3 (m.d 3 4) (by simp) with h16437 | h16437
                                                      · rcases p16415_3 (m.d 3 5) (by simp) with h16438 | h16438
                                                        · linarith only [h16190, h16438, hlam]
                                                        · linarith only [h16013, h16438, hlam]
                                                      · linarith only [h16437, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                rcases p16415_3 (m.d 0 3) (by simp) with h16442 | h16442
                                                · linarith only [h15538, h16442, hlam]
                                                · linarith only [h15532, h16442, hlam]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                rcases p16415_3 (m.d 0 3) (by simp) with h16445 | h16445
                                                · linarith only [h15538, h16445, hlam]
                                                · linarith only [h15535, h16445, hlam]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16013, hc03, hc34, hlam, hphi, p16415_1]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                rcases p16415_3 (m.d 0 3) (by simp) with h16450 | h16450
                                                · linarith only [h16450, hlam, p16415_0]
                                                · rcases p16415_3 (m.d 1 3) (by simp) with h16452 | h16452
                                                  · linarith only [h16182, h16452, hlam]
                                                  · rcases p16415_3 (m.d 2 3) (by simp) with h16454 | h16454
                                                    · linarith only [h16187, h16454, hlam]
                                                    · rcases p16415_3 (m.d 3 4) (by simp) with h16456 | h16456
                                                      · rcases p16415_3 (m.d 3 5) (by simp) with h16457 | h16457
                                                        · rcases h5bigk with h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c | h16458c
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h0, h15533, h16176, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h0, h15533, h16176, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16013, hlam, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h0, h15533, h16176, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h15534, hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h0, h15534, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16182, hlam, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h0, h15533, h16184, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h15537, hlam, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16179, hlam, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16187, hlam, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h15537, hc02, hc45, hlam, hphi, ht0b, ht5b, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h15532, h16177, hc23, hc35, hlam, hphi, p16191_1, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16177, h16182, hc23, hc35, hlam, hphi, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16187, hc23, hc35, hlam, hphi, p16458_1]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            rcases p16458_3 (m.d 0 5) (by simp) with h16478 | h16478
                                                            · linarith only [h16013, h16478, hlam]
                                                            · linarith only [h16176, h16478, hlam]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16176, hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16184, hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16189, hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [h16190, hlam, p16458_0]
                                                          · have p16458_0 := h16458c.1
                                                            have p16458_1 := h16458c.2.1
                                                            have p16458_2 := h16458c.2.2.1
                                                            have p16458_3 := h16458c.2.2.2
                                                            linarith only [hlam, p16458_0]
                                                        · linarith only [h16457, hlam, p16415_0]
                                                      · linarith only [h15538, h16456, hlam]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                rcases p16415_3 (m.d 0 3) (by simp) with h16488 | h16488
                                                · linarith only [h16013, h16488, hlam]
                                                · linarith only [h15532, h16488, hlam]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                rcases p16415_3 (m.d 0 3) (by simp) with h16491 | h16491
                                                · linarith only [h16013, h16491, hlam]
                                                · linarith only [h15535, h16491, hlam]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [h16190, hlam, p16415_0]
                                              · have p16415_0 := h16415c.1
                                                have p16415_1 := h16415c.2.1
                                                have p16415_2 := h16415c.2.2.1
                                                have p16415_3 := h16415c.2.2.2
                                                linarith only [hlam, p16415_0]
                                      · linarith only [h16178, h16408, hlam]
                                    · linarith only [h16407, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    rcases p16395_3 (m.d 0 2) (by simp) with h16498 | h16498
                                    · rcases p16395_3 (m.d 1 2) (by simp) with h16499 | h16499
                                      · rcases p16395_3 (m.d 2 3) (by simp) with h16500 | h16500
                                        · linarith only [h15535, h16500, hlam]
                                        · rcases p16395_3 (m.d 2 4) (by simp) with h16502 | h16502
                                          · linarith only [h15536, h16502, hlam]
                                          · linarith only [h16189, h16502, hlam]
                                      · linarith only [h16179, h16499, hlam]
                                    · linarith only [h16498, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h0, h15532, h15534, h16177, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16191_1, p16395_1]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h0, h15532, h15533, h16176, h16177, hlam, p16191_1, p16395_2]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    rcases p16395_3 (m.d 0 2) (by simp) with h16510 | h16510
                                    · linarith only [h0, h16510, hlam]
                                    · linarith only [h15536, h16510, hlam]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    rcases p16395_3 (m.d 0 2) (by simp) with h16513 | h16513
                                    · linarith only [h0, h16513, hlam]
                                    · linarith only [h15537, h16513, hlam]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h15535, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h16177, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h16185, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h16187, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h15536, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h16178, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h0, h15533, h16178, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16395_1]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h0, h15533, h16178, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16395_1]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h15537, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h16179, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h0, h15534, h16179, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16395_1]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [h16189, hlam, p16395_0]
                                  · have p16395_0 := h16395c.1
                                    have p16395_1 := h16395c.2.1
                                    have p16395_2 := h16395c.2.2.1
                                    have p16395_3 := h16395c.2.2.2
                                    linarith only [hlam, p16395_0]
                                · linarith only [h16013, h16394, hlam]
                              · linarith only [h15538, h16393, hlam]
                          · linarith only [h15535, h16390, hlam]
                        · linarith only [h15532, h16389, hlam]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [h16176, hlam, p16191_1]
                      · have p16191_0 := h16191c.1
                        have p16191_1 := h16191c.2.1
                        have p16191_2 := h16191c.2.2.1
                        have p16191_3 := h16191c.2.2.2
                        linarith only [hlam, p16191_0]
                    · linarith only [h15538, h16176, h16190, hlam]
                  · linarith only [h0, h15533, h16184, h16189, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16539 | h16539
              · linarith only [h15538, h16176, h16177, h16180, h16184, h16539, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16541 | h16541
                · linarith only [h0, h15533, h16176, h16177, h16180, h16184, h16541, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16543 | h16543
                  · linarith only [h16178, h16184, h16543, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16545 | h16545
                    · rcases h0bigk with h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c | h16546c
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [hlam, p16546_0]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h0, hlam, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        rcases p16546_3 (m.d 0 1) (by simp) with h16549 | h16549
                        · rcases p16546_3 (m.d 0 2) (by simp) with h16550 | h16550
                          · rcases p16546_3 (m.d 0 3) (by simp) with h16551 | h16551
                            · linarith only [h15532, h16551, hlam]
                            · rcases p16546_3 (m.d 0 4) (by simp) with h16553 | h16553
                              · linarith only [h15533, h16553, hlam]
                              · linarith only [h15538, h16553, hlam]
                          · linarith only [h15535, h16550, hlam]
                        · linarith only [h15532, h16549, hlam]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h0, h16176, h16184, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h0, h16176, h16178, h16184, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h0, h15533, h16176, h16178, h16184, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [hlam, p16546_0]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        rcases p16546_3 (m.d 0 1) (by simp) with h16562 | h16562
                        · linarith only [h0, h16562, hlam]
                        · linarith only [h15532, h16562, hlam]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h16176, h16177, h16180, h16184, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        rcases p16546_3 (m.d 0 1) (by simp) with h16566 | h16566
                        · linarith only [h0, h16566, hlam]
                        · linarith only [h15534, h16566, hlam]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15532, hlam, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15535, hlam, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [hlam, p16546_0]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15538, hlam, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h16013, hlam, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15533, hlam, p16546_0]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15536, hlam, p16546_0]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        rcases p16546_3 (m.d 0 1) (by simp) with h16576 | h16576
                        · rcases p16546_3 (m.d 0 2) (by simp) with h16577 | h16577
                          · rcases p16546_3 (m.d 0 3) (by simp) with h16578 | h16578
                            · linarith only [h15538, h16578, hlam]
                            · rcases p16546_3 (m.d 0 4) (by simp) with h16580 | h16580
                              · rcases p16546_3 (m.d 0 5) (by simp) with h16581 | h16581
                                · linarith only [h16176, h16581, hlam]
                                · linarith only [h16013, h16581, hlam]
                              · linarith only [h15538, h16580, hlam]
                          · linarith only [h15535, h16577, hlam]
                        · linarith only [h15532, h16576, hlam]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [hlam, p16546_0]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15538, h16176, h16177, h16180, h16184, hc23, hc34, hlam, hphi, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15534, hlam, p16546_0]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h15537, hlam, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        rcases p16546_3 (m.d 0 1) (by simp) with h16591 | h16591
                        · rcases p16546_3 (m.d 0 2) (by simp) with h16592 | h16592
                          · rcases p16546_3 (m.d 0 3) (by simp) with h16593 | h16593
                            · linarith only [h16013, h16593, hlam]
                            · rcases p16546_3 (m.d 0 4) (by simp) with h16595 | h16595
                              · rcases p16546_3 (m.d 0 5) (by simp) with h16596 | h16596
                                · rcases h2bigk with h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c | h16597c
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h0, hlam, p16597_1]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    rcases p16597_3 (m.d 0 2) (by simp) with h16600 | h16600
                                    · rcases p16597_3 (m.d 1 2) (by simp) with h16601 | h16601
                                      · rcases p16597_3 (m.d 2 3) (by simp) with h16602 | h16602
                                        · linarith only [h16602, hlam, p16597_0]
                                        · rcases p16597_3 (m.d 2 4) (by simp) with h16604 | h16604
                                          · linarith only [h15536, h16604, hlam]
                                          · linarith only [h16539, h16604, hlam]
                                      · linarith only [h16177, h16601, hlam]
                                    · linarith only [h16600, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    rcases p16597_3 (m.d 0 2) (by simp) with h16609 | h16609
                                    · rcases p16597_3 (m.d 1 2) (by simp) with h16610 | h16610
                                      · rcases p16597_3 (m.d 2 3) (by simp) with h16611 | h16611
                                        · linarith only [h15535, h16611, hlam]
                                        · rcases p16597_3 (m.d 2 4) (by simp) with h16613 | h16613
                                          · linarith only [h16613, hlam, p16597_0]
                                          · rcases p16597_3 (m.d 2 5) (by simp) with h16615 | h16615
                                            · linarith only [h15537, h16615, hlam]
                                            · linarith only [h16543, h16615, hlam]
                                      · linarith only [h16178, h16610, hlam]
                                    · linarith only [h16609, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    rcases p16597_3 (m.d 0 2) (by simp) with h16620 | h16620
                                    · rcases p16597_3 (m.d 1 2) (by simp) with h16621 | h16621
                                      · rcases p16597_3 (m.d 2 3) (by simp) with h16622 | h16622
                                        · linarith only [h15535, h16622, hlam]
                                        · rcases p16597_3 (m.d 2 4) (by simp) with h16624 | h16624
                                          · linarith only [h15536, h16624, hlam]
                                          · rcases p16597_3 (m.d 2 5) (by simp) with h16626 | h16626
                                            · linarith only [h16626, hlam, p16597_0]
                                            · rcases h3bigk with h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c | h16628c
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16177, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16546_1, p16628_1]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h0, h15534, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16546_1, p16628_1]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h15538, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16013, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h15532, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16180, h16184, hc23, hc45, hlam, hphi, ht34, p16628_1]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16180, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16182, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h15535, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16177, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16539, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16541, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                rcases p16628_3 (m.d 0 3) (by simp) with h16644 | h16644
                                                · linarith only [h16644, hlam, p16628_0]
                                                · rcases p16628_3 (m.d 1 3) (by simp) with h16646 | h16646
                                                  · linarith only [h16180, h16646, hlam]
                                                  · rcases p16628_3 (m.d 2 3) (by simp) with h16648 | h16648
                                                    · linarith only [h16539, h16648, hlam]
                                                    · rcases p16628_3 (m.d 3 4) (by simp) with h16650 | h16650
                                                      · rcases p16628_3 (m.d 3 5) (by simp) with h16651 | h16651
                                                        · linarith only [h16545, h16651, hlam]
                                                        · linarith only [h16013, h16651, hlam]
                                                      · linarith only [h16650, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                rcases p16628_3 (m.d 0 3) (by simp) with h16655 | h16655
                                                · linarith only [h15538, h16655, hlam]
                                                · linarith only [h15532, h16655, hlam]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                rcases p16628_3 (m.d 0 3) (by simp) with h16658 | h16658
                                                · linarith only [h15538, h16658, hlam]
                                                · linarith only [h15535, h16658, hlam]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16013, hc03, hc34, hlam, hphi, p16628_1]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                rcases p16628_3 (m.d 0 3) (by simp) with h16663 | h16663
                                                · linarith only [h16663, hlam, p16628_0]
                                                · rcases p16628_3 (m.d 1 3) (by simp) with h16665 | h16665
                                                  · linarith only [h16182, h16665, hlam]
                                                  · rcases p16628_3 (m.d 2 3) (by simp) with h16667 | h16667
                                                    · linarith only [h16541, h16667, hlam]
                                                    · rcases p16628_3 (m.d 3 4) (by simp) with h16669 | h16669
                                                      · rcases p16628_3 (m.d 3 5) (by simp) with h16670 | h16670
                                                        · rcases h5bigk with h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c | h16671c
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [hlam, p16671_0]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h0, h15534, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h0, h15534, h16539, h16543, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16013, hlam, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h0, h15533, h16176, h16184, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h15534, hlam, p16671_0]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [hlam, p16671_0]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h0, h15534, h16539, h16543, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16182, hlam, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16184, hlam, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h15537, hlam, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16179, hlam, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [hlam, p16671_0]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16541, hlam, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16543, hlam, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h15537, h16539, h16543, hc23, hc35, hlam, hphi, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16179, h16539, h16543, hc23, hc35, hlam, hphi, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16539, h16543, hc23, hc35, hlam, hphi, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [hlam, p16671_0]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16178, h16184, h16539, h16545, hc23, hc34, hlam, hphi, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16176, hlam, p16671_0]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16179, h16539, h16543, hc23, hc45, hlam, hphi, ht34, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h0, h15533, h16176, h16539, h16543, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16671_1]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [h16545, hlam, p16671_0]
                                                          · have p16671_0 := h16671c.1
                                                            have p16671_1 := h16671c.2.1
                                                            have p16671_2 := h16671c.2.2.1
                                                            have p16671_3 := h16671c.2.2.2
                                                            linarith only [hlam, p16671_0]
                                                        · linarith only [h16670, hlam, p16628_0]
                                                      · linarith only [h15538, h16669, hlam]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                rcases p16628_3 (m.d 0 3) (by simp) with h16699 | h16699
                                                · linarith only [h16013, h16699, hlam]
                                                · linarith only [h15532, h16699, hlam]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                rcases p16628_3 (m.d 0 3) (by simp) with h16702 | h16702
                                                · linarith only [h16013, h16702, hlam]
                                                · linarith only [h15535, h16702, hlam]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [h16545, hlam, p16628_0]
                                              · have p16628_0 := h16628c.1
                                                have p16628_1 := h16628c.2.1
                                                have p16628_2 := h16628c.2.2.1
                                                have p16628_3 := h16628c.2.2.2
                                                linarith only [hlam, p16628_0]
                                      · linarith only [h16179, h16621, hlam]
                                    · linarith only [h16620, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h0, h15532, h15534, h16177, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16546_1, p16597_1]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h0, h15532, h15533, h16176, h16177, hlam, p16546_1, p16597_2]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h0, h15533, h16176, h16178, h16184, hlam, p16597_2]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    rcases p16597_3 (m.d 0 2) (by simp) with h16713 | h16713
                                    · linarith only [h0, h16713, hlam]
                                    · linarith only [h15537, h16713, hlam]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h15535, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h16177, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h16539, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h16541, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h15536, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h16178, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h15533, h16176, h16178, h16184, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16597_1]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h16543, hlam, p16597_1]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h15537, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h16179, hlam, p16597_0]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h0, h15534, h16179, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16597_1]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [h0, h15533, h16176, h16179, h16184, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16597_1]
                                  · have p16597_0 := h16597c.1
                                    have p16597_1 := h16597c.2.1
                                    have p16597_2 := h16597c.2.2.1
                                    have p16597_3 := h16597c.2.2.2
                                    linarith only [hlam, p16597_0]
                                · linarith only [h16013, h16596, hlam]
                              · linarith only [h15538, h16595, hlam]
                          · linarith only [h15535, h16592, hlam]
                        · linarith only [h15532, h16591, hlam]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [h16176, hlam, p16546_1]
                      · have p16546_0 := h16546c.1
                        have p16546_1 := h16546c.2.1
                        have p16546_2 := h16546c.2.2.1
                        have p16546_3 := h16546c.2.2.2
                        linarith only [hlam, p16546_0]
                    · linarith only [h0, h15532, h15533, h15538, h16176, h16177, h16545, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h15533, h15537, h16176, h16179, hc02, hc45, hlam, hphi, ht0b, ht5b]
    · linarith only [h0, h15536, h16178, hlam]
  · linarith only [h0, h15535, h16177, hlam]

end R2N4
