import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4335 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 2 4 (by decide) (by decide) with h6194 | h6194
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6195 | h6195
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6196 | h6196
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6197 | h6197
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6198 | h6198
          · linarith only [h4335, h6194, h6198, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6200 | h6200
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6201 | h6201
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6202 | h6202
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6203 | h6203
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6204 | h6204
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6205 | h6205
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6206 | h6206
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6207 | h6207
                          · linarith only [h0, h6194, h6198, h6207, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                          · linarith only [h4044, h6197, h6198, h6200, h6207, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h6195, h6198, h6206, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h6195, h6198, h6205, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h4044, h6197, h6204, hlam]
                  · linarith only [h0, h6194, h6196, h6197, h6198, h6203, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h6198, h6200, h6202, hlam]
              · linarith only [h0, h6195, h6201, hlam]
            · linarith only [h0, h6194, h6200, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6217 | h6217
          · linarith only [h4335, h6194, h6217, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6219 | h6219
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6220 | h6220
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6221 | h6221
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6222 | h6222
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6223 | h6223
                    · linarith only [h6197, h6217, h6219, h6223, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6225 | h6225
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6226 | h6226
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6227 | h6227
                          · linarith only [h6194, h6223, h6227, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6229 | h6229
                            · linarith only [h0, h4044, h6195, h6217, h6223, h6225, h6227, h6229, hc01, hc23, hlam, hphi, ht12]
                            · rcases h1bigk with h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c | h6231c
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h0, hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h3473, hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h4044, hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h4238, hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6217, hc01, hc23, hlam, hphi, ht12, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6217, hlam, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h4044, h6217, hc01, hc23, hlam, hphi, ht12, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h4238, h6217, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6231_1, u5ehi0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                rcases p6231_3 (m.d 0 1) (by simp) with h6242 | h6242
                                · linarith only [h6242, hlam, p6231_0]
                                · rcases p6231_3 (m.d 1 2) (by simp) with h6244 | h6244
                                  · linarith only [h6217, h6244, hlam]
                                  · linarith only [h0, h6244, hlam]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h0, h6195, h6225, h6227, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p6231_1, u4ehi3]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h4044, h6217, hc01, hc23, hlam, hphi, ht12, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h4044, h6217, h6223, hc01, hc23, hlam, hphi, ht12, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6223, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6219, hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6221, hlam, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6223, hlam, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6217, h6220, hc01, hc23, hlam, hphi, ht12, p6231_1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6220, hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6222, hlam, p6231_0]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [h6217, h6220, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6231_1, u4ehi1]
                              · have p6231_0 := h6231c.1
                                have p6231_1 := h6231c.2.1
                                have p6231_2 := h6231c.2.2.1
                                have p6231_3 := h6231c.2.2.2
                                linarith only [hlam, p6231_0]
                        · linarith only [h0, h6195, h6217, h6226, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h6194, h6217, h6225, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h3473, h4335, h6195, h6196, h6222, hlam]
                · linarith only [h6217, h6219, h6221, hlam]
              · linarith only [h0, h6195, h6220, hlam]
            · linarith only [h0, h6194, h6219, hlam]
      · linarith only [h4335, h6195, h6196, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6268 | h6268
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6269 | h6269
        · linarith only [h6194, h6195, h6269, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6271 | h6271
          · linarith only [h4335, h6194, h6271, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6273 | h6273
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6274 | h6274
              · linarith only [h6194, h6195, h6274, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6276 | h6276
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6277 | h6277
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6278 | h6278
                    · linarith only [h6269, h6271, h6273, h6278, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6280 | h6280
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6281 | h6281
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6282 | h6282
                          · linarith only [h6194, h6278, h6282, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h0, h6194, h6274, h6282, hc45, hlam, hphi, u4ehi2]
                        · linarith only [h4335, h6194, h6268, h6280, h6281, hc05, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h6271, h6280, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h3473, h6268, h6277, hlam]
                · linarith only [h6271, h6273, h6276, hlam]
            · linarith only [h0, h4238, h6194, h6195, h6273, hc01, hc15, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6290 | h6290
        · linarith only [h4335, h6194, h6268, h6290, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6292 | h6292
          · linarith only [h4335, h6194, h6292, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6294 | h6294
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6295 | h6295
              · linarith only [h6194, h6195, h6295, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6297 | h6297
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6298 | h6298
                  · linarith only [h4335, h6194, h6268, h6292, h6298, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6300 | h6300
                    · linarith only [h6290, h6292, h6294, h6298, h6300, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6302 | h6302
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6303 | h6303
                        · linarith only [h0, h6292, h6298, h6303, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h4335, h6194, h6302, h6303, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h6194, h6292, h6302, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h6292, h6294, h6297, hlam]
            · linarith only [h0, h6194, h6294, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6309 | h6309
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6310 | h6310
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6311 | h6311
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6312 | h6312
          · linarith only [h4335, h6309, h6312, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6314 | h6314
            · linarith only [h6194, h6309, h6312, h6314, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6316 | h6316
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6317 | h6317
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6318 | h6318
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6319 | h6319
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6320 | h6320
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6321 | h6321
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6322 | h6322
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6323 | h6323
                            · rcases h1bigk with h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c | h6324c
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h0, hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h3473, hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h4044, hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h4238, hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6314, h6320, hc01, hc23, hlam, hphi, ht12, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6312, hlam, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6314, hlam, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6314, h6320, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6324_1, u5ehi1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                rcases p6324_3 (m.d 0 1) (by simp) with h6335 | h6335
                                · linarith only [h6335, hlam, p6324_0]
                                · rcases p6324_3 (m.d 1 2) (by simp) with h6337 | h6337
                                  · linarith only [h6312, h6337, hlam]
                                  · linarith only [h0, h6337, hlam]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h0, h6309, h6312, h6314, h6321, h6323, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6324_1, u4ehi4]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h4238, h6312, hc01, hc23, hlam, hphi, ht12, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                rcases p6324_3 (m.d 0 1) (by simp) with h6344 | h6344
                                · linarith only [h6344, hlam, p6324_0]
                                · rcases p6324_3 (m.d 1 2) (by simp) with h6346 | h6346
                                  · linarith only [h6314, h6346, hlam]
                                  · linarith only [h0, h6346, hlam]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h0, h6309, h6321, h6323, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6324_1, u4ehi4]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6317, hlam, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h4238, h6314, h6320, hc01, hc23, hlam, hphi, ht12, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6312, h6316, hc01, hc23, hlam, hphi, ht12, p6324_1]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6316, hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6318, hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [h6319, hlam, p6324_0]
                              · have p6324_0 := h6324c.1
                                have p6324_1 := h6324c.2.1
                                have p6324_2 := h6324c.2.2.1
                                have p6324_3 := h6324c.2.2.2
                                linarith only [hlam, p6324_0]
                            · linarith only [h0, h6309, h6314, h6320, h6322, h6323, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h6309, h6311, h6314, h6322, hc04, hlam, hphi, ht0b, ht5b, u5ehi0]
                        · linarith only [h0, h6309, h6310, h6314, h6320, h6321, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h4335, h6309, h6320, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h4044, h4238, h6311, h6314, h6316, h6319, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h3473, h6310, h6318, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6364 | h6364
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6365 | h6365
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6366 | h6366
                      · linarith only [h3473, h4335, h6309, h6317, h6366, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h4335, h6309, h6366, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h4044, h6309, h6311, h6312, h6365, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h3473, h6310, h6364, hlam]
              · linarith only [h0, h3473, h4335, h6309, h6316, hc01, hc13, hlam, hphi]
        · linarith only [h6194, h6309, h6311, hlam]
      · linarith only [h4335, h6309, h6310, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6374 | h6374
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6375 | h6375
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6376 | h6376
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6377 | h6377
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6378 | h6378
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6379 | h6379
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6380 | h6380
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6381 | h6381
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6382 | h6382
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6383 | h6383
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6384 | h6384
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6385 | h6385
                            · linarith only [h6376, h6382, h6385, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h6194, h6375, h6376, h6382, h6385, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h6194, h6375, h6384, hlam]
                        · linarith only [h6194, h6374, h6375, h6382, h6383, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · linarith only [h4335, h6374, h6376, h6379, h6382, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h4044, h6194, h6375, h6381, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h3473, h6374, h6380, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6393 | h6393
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6394 | h6394
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6395 | h6395
                      · linarith only [h6376, h6379, h6395, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6397 | h6397
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6398 | h6398
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6399 | h6399
                            · rcases h1bigk with h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c | h6400c
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h0, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h3473, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h4044, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h4238, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                rcases p6400_3 (m.d 0 1) (by simp) with h6406 | h6406
                                · linarith only [h6406, hlam, p6400_0]
                                · rcases p6400_3 (m.d 1 2) (by simp) with h6408 | h6408
                                  · rcases p6400_3 (m.d 1 3) (by simp) with h6409 | h6409
                                    · linarith only [h6376, h6409, hlam]
                                    · linarith only [h3473, h6409, hlam]
                                  · linarith only [h6408, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h4335, h6374, h6376, hc12, hlam, hphi, ht01, ht0b, ht5b, p6400_1, u5ehi3]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h4044, hc01, hc12, hlam, hphi, p6400_1]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h4238, hc01, hc12, hlam, hphi, p6400_1]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6379, hc01, hc34, hlam, hphi, ht12, ht23, p6400_1]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6376, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6379, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h0, h6309, h6378, hc01, hc13, hlam, hphi, p6400_1]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                rcases p6400_3 (m.d 0 1) (by simp) with h6422 | h6422
                                · linarith only [h6422, hlam, p6400_0]
                                · rcases p6400_3 (m.d 1 2) (by simp) with h6424 | h6424
                                  · rcases p6400_3 (m.d 1 3) (by simp) with h6425 | h6425
                                    · linarith only [h6379, h6425, hlam]
                                    · linarith only [h3473, h6425, hlam]
                                  · linarith only [h0, h6424, hlam]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6377, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h3473, h6379, hc01, hc34, hlam, hphi, ht12, ht23, p6400_1]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h0, h6309, h6378, h6379, hc01, hc34, hlam, hphi, ht12, ht23, p6400_1]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6379, h6393, hc01, hc34, hlam, hphi, ht12, ht23, p6400_1]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6378, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6393, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [h6394, hlam, p6400_0]
                              · have p6400_0 := h6400c.1
                                have p6400_1 := h6400c.2.1
                                have p6400_2 := h6400c.2.2.1
                                have p6400_3 := h6400c.2.2.2
                                linarith only [hlam, p6400_0]
                            · linarith only [h6375, h6379, h6393, h6399, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h6194, h6375, h6398, hlam]
                        · linarith only [h4335, h6374, h6397, hlam]
                    · linarith only [h6194, h6375, h6377, h6394, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h4335, h6374, h6376, h6393, hlam]
              · linarith only [h6194, h6375, h6377, h6378, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h4335, h6374, h6376, h6377, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6445 | h6445
            · linarith only [h0, h6194, h6376, h6445, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6447 | h6447
              · linarith only [h0, h6309, h6376, h6447, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6449 | h6449
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6450 | h6450
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6451 | h6451
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6452 | h6452
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6453 | h6453
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6454 | h6454
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6455 | h6455
                            · rcases h1bigk with h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h0, hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h3473, hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h4044, hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h4238, hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h6447, h6452, h6454, hc01, hc23, hlam, hphi, ht12, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h6376, hlam, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h6445, hlam, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h6447, hlam, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                rcases p6456_3 (m.d 0 1) (by simp) with h6467 | h6467
                                · linarith only [h6467, hlam, p6456_0]
                                · rcases p6456_3 (m.d 1 2) (by simp) with h6469 | h6469
                                  · linarith only [h6376, h6469, hlam]
                                  · linarith only [h0, h6469, hlam]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h4044, h6376, hc01, hc23, hlam, hphi, ht12, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h0, h6376, h6447, hc01, hc23, hlam, hphi, ht12, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                rcases p6456_3 (m.d 0 1) (by simp) with h6476 | h6476
                                · linarith only [h6476, hlam, p6456_0]
                                · rcases p6456_3 (m.d 1 2) (by simp) with h6478 | h6478
                                  · linarith only [h6445, h6478, hlam]
                                  · linarith only [h0, h6478, hlam]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h6449, hlam, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h0, h6445, h6447, h6452, hc01, hc23, hlam, hphi, ht12, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                rcases p6456_3 (m.d 0 1) (by simp) with h6485 | h6485
                                · linarith only [h6485, hlam, p6456_0]
                                · rcases p6456_3 (m.d 1 2) (by simp) with h6487 | h6487
                                  · linarith only [h6447, h6487, hlam]
                                  · linarith only [h0, h6487, hlam]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p6456_1]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h6450, hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [h6451, hlam, p6456_0]
                              · have p6456_0 := h6456c.1
                                have p6456_1 := h6456c.2.1
                                have p6456_2 := h6456c.2.2.1
                                have p6456_3 := h6456c.2.2.2
                                linarith only [hlam, p6456_0]
                            · rcases h1bigk with h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c | h6494c
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h0, hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h3473, hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h4044, hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h4238, hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h6376, hc01, hc23, hlam, hphi, ht12, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h6376, hlam, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h6445, hlam, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h6447, hlam, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                rcases p6494_3 (m.d 0 1) (by simp) with h6505 | h6505
                                · linarith only [h6505, hlam, p6494_0]
                                · rcases p6494_3 (m.d 1 2) (by simp) with h6507 | h6507
                                  · linarith only [h6376, h6507, hlam]
                                  · linarith only [h0, h6507, hlam]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h0, h6376, hc01, hc23, hlam, hphi, ht12, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h4044, h6376, hc01, hc23, hlam, hphi, ht12, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h4238, h6376, hc01, hc23, hlam, hphi, ht12, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                rcases p6494_3 (m.d 0 1) (by simp) with h6514 | h6514
                                · linarith only [h6514, hlam, p6494_0]
                                · rcases p6494_3 (m.d 1 2) (by simp) with h6516 | h6516
                                  · linarith only [h6445, h6516, hlam]
                                  · linarith only [h0, h6516, hlam]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h6449, hlam, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h4238, h6375, h6445, h6452, h6455, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6494_1, u4ehi3]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                rcases p6494_3 (m.d 0 1) (by simp) with h6523 | h6523
                                · linarith only [h6523, hlam, p6494_0]
                                · rcases p6494_3 (m.d 1 2) (by simp) with h6525 | h6525
                                  · linarith only [h6447, h6525, hlam]
                                  · linarith only [h0, h6525, hlam]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p6494_1]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h6450, hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [h6451, hlam, p6494_0]
                              · have p6494_0 := h6494c.1
                                have p6494_1 := h6494c.2.1
                                have p6494_2 := h6494c.2.2.1
                                have p6494_3 := h6494c.2.2.2
                                linarith only [hlam, p6494_0]
                          · linarith only [h4044, h6375, h6445, h6454, hlam]
                        · linarith only [h0, h6445, h6452, h6453, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h6376, h6452, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4044, h6375, h6451, hlam]
                  · linarith only [h4044, h6374, h6375, h6449, h6450, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6537 | h6537
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6538 | h6538
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6539 | h6539
                      · linarith only [h3473, h6374, h6449, h6539, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h6376, h6539, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4044, h6375, h6538, hlam]
                  · linarith only [h3473, h6374, h6537, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6544 | h6544
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6545 | h6545
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6546 | h6546
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6547 | h6547
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6548 | h6548
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6549 | h6549
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6550 | h6550
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6551 | h6551
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6552 | h6552
                          · linarith only [h6375, h6545, h6552, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h6194, h6547, h6549, h6552, hc01, hc13, hlam, hphi]
                        · linarith only [h6374, h6550, h6551, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h4335, h6374, h6544, h6547, h6550, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6557 | h6557
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6558 | h6558
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6559 | h6559
                          · linarith only [h6545, h6549, h6559, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6561 | h6561
                            · linarith only [h6194, h6545, h6549, h6557, h6561, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · rcases h1bigk with h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c | h6563c
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h0, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h3473, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h4044, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h4238, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                rcases p6563_3 (m.d 0 1) (by simp) with h6569 | h6569
                                · linarith only [h6569, hlam, p6563_0]
                                · rcases p6563_3 (m.d 1 2) (by simp) with h6571 | h6571
                                  · rcases p6563_3 (m.d 1 3) (by simp) with h6572 | h6572
                                    · linarith only [h6544, h6572, hlam]
                                    · linarith only [h3473, h6572, hlam]
                                  · linarith only [h6571, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h3473, hc01, hc12, hlam, hphi, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h0, h6194, h6545, hc01, hc12, hlam, hphi, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h4238, hc01, hc12, hlam, hphi, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                rcases p6563_3 (m.d 0 1) (by simp) with h6580 | h6580
                                · linarith only [h6580, hlam, p6563_0]
                                · rcases p6563_3 (m.d 1 2) (by simp) with h6582 | h6582
                                  · rcases p6563_3 (m.d 1 3) (by simp) with h6583 | h6583
                                    · rcases p6563_3 (m.d 1 4) (by simp) with h6584 | h6584
                                      · linarith only [h6547, h6584, hlam]
                                      · linarith only [h4044, h6584, hlam]
                                    · linarith only [h6583, hlam, p6563_0]
                                  · linarith only [h0, h6582, hlam]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h6544, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h0, h6194, h6545, hc01, hc13, hlam, hphi, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h0, h6194, h6544, h6546, h6559, hc01, hc12, hlam, hphi, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h6549, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h6545, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h6547, hlam, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h6549, hlam, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                rcases p6563_3 (m.d 0 1) (by simp) with h6598 | h6598
                                · linarith only [h6598, hlam, p6563_0]
                                · rcases p6563_3 (m.d 1 2) (by simp) with h6600 | h6600
                                  · rcases p6563_3 (m.d 1 3) (by simp) with h6601 | h6601
                                    · rcases p6563_3 (m.d 1 4) (by simp) with h6602 | h6602
                                      · linarith only [h6549, h6602, hlam]
                                      · linarith only [h4044, h6602, hlam]
                                    · linarith only [h3473, h6601, hlam]
                                  · linarith only [h0, h6600, hlam]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h6546, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h6548, hlam, p6563_0]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [h4044, hc01, hc15, hlam, hphi, p6563_1]
                              · have p6563_0 := h6563c.1
                                have p6563_1 := h6563c.2.1
                                have p6563_2 := h6563c.2.2.1
                                have p6563_3 := h6563c.2.2.2
                                linarith only [hlam, p6563_0]
                        · linarith only [h4335, h6374, h6558, hlam]
                      · linarith only [h4335, h6374, h6544, h6547, h6557, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · linarith only [h3473, h4335, h6374, h6548, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6614 | h6614
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6615 | h6615
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6616 | h6616
                      · linarith only [h6544, h6547, h6616, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6618 | h6618
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6619 | h6619
                          · linarith only [h6375, h6545, h6619, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h6194, h6615, h6619, hc01, hc14, hlam, hphi]
                        · linarith only [h4335, h6374, h6618, hlam]
                    · linarith only [h6547, h6614, h6615, hlam]
                  · linarith only [h4335, h6374, h6544, h6614, hlam]
              · linarith only [h4335, h6374, h6544, h6546, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h4335, h6374, h6544, h6545, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6627 | h6627
            · linarith only [h0, h6194, h6544, h6627, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6629 | h6629
              · linarith only [h0, h6309, h6544, h6629, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6631 | h6631
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6632 | h6632
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6633 | h6633
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6634 | h6634
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6635 | h6635
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6636 | h6636
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6637 | h6637
                            · linarith only [h6375, h6631, h6637, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · rcases h1bigk with h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c | h6639c
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h0, hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h3473, hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h4044, hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h4238, hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6629, h6634, h6636, hc01, hc23, hlam, hphi, ht12, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6544, hlam, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6627, hlam, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6629, hlam, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                rcases p6639_3 (m.d 0 1) (by simp) with h6650 | h6650
                                · linarith only [h6650, hlam, p6639_0]
                                · rcases p6639_3 (m.d 1 2) (by simp) with h6652 | h6652
                                  · linarith only [h6544, h6652, hlam]
                                  · linarith only [h0, h6652, hlam]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h0, h6544, hc01, hc23, hlam, hphi, ht12, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6375, h6544, h6633, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6639_1, u4ehi0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h4238, h6544, hc01, hc23, hlam, hphi, ht12, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                rcases p6639_3 (m.d 0 1) (by simp) with h6659 | h6659
                                · linarith only [h6659, hlam, p6639_0]
                                · rcases p6639_3 (m.d 1 2) (by simp) with h6661 | h6661
                                  · linarith only [h6627, h6661, hlam]
                                  · linarith only [h0, h6661, hlam]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6631, hlam, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6375, h6627, h6633, h6634, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6639_1, u4ehi0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                rcases p6639_3 (m.d 0 1) (by simp) with h6668 | h6668
                                · linarith only [h6668, hlam, p6639_0]
                                · rcases p6639_3 (m.d 1 2) (by simp) with h6670 | h6670
                                  · linarith only [h6629, h6670, hlam]
                                  · linarith only [h0, h6670, hlam]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p6639_1]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6632, hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [h6633, hlam, p6639_0]
                              · have p6639_0 := h6639c.1
                                have p6639_1 := h6639c.2.1
                                have p6639_2 := h6639c.2.2.1
                                have p6639_3 := h6639c.2.2.2
                                linarith only [hlam, p6639_0]
                          · linarith only [h0, h6627, h6636, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h6375, h6544, h6631, h6633, h6635, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · linarith only [h6375, h6544, h6631, h6633, h6634, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6680 | h6680
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6681 | h6681
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6682 | h6682
                          · linarith only [h4044, h6633, h6680, h6682, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h6627, h6682, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h3473, h4335, h6374, h6681, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h6544, h6680, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h6374, h6631, h6632, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6688 | h6688
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6689 | h6689
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6690 | h6690
                      · linarith only [h6375, h6631, h6688, h6689, h6690, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h6544, h6690, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h6631, h6688, h6689, hlam]
                  · linarith only [h3473, h6374, h6688, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6695 | h6695
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6696 | h6696
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6697 | h6697
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6698 | h6698
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6699 | h6699
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6700 | h6700
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6701 | h6701
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6702 | h6702
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6703 | h6703
                        · linarith only [h0, h4335, h6374, h6696, h6703, hc01, hc12, hlam, hphi]
                        · linarith only [h6700, h6702, h6703, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h4335, h6696, h6699, h6702, hc01, hc12, hlam, hphi]
                    · linarith only [h6194, h6695, h6697, h6701, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6708 | h6708
                    · linarith only [h6699, h6700, h6708, hlam]
                    · linarith only [h6194, h6695, h6697, h6708, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6711 | h6711
                  · linarith only [h0, h4335, h6374, h6699, h6711, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6713 | h6713
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6714 | h6714
                      · linarith only [h3473, h6699, h6714, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6716 | h6716
                        · linarith only [h6696, h6711, h6716, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6718 | h6718
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6719 | h6719
                            · rcases h1bigk with h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c | h6720c
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h0, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h3473, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h4044, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h4238, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                rcases p6720_3 (m.d 0 1) (by simp) with h6726 | h6726
                                · linarith only [h6726, hlam, p6720_0]
                                · rcases p6720_3 (m.d 1 2) (by simp) with h6728 | h6728
                                  · rcases p6720_3 (m.d 1 3) (by simp) with h6729 | h6729
                                    · linarith only [h6696, h6729, hlam]
                                    · linarith only [h3473, h6729, hlam]
                                  · linarith only [h6728, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h0, h4335, h6696, hc01, hc12, hlam, hphi, p6720_1]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6194, h6695, h6697, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6720_1, u4ehi4]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h0, h4335, h6696, h6711, hc01, hc12, hlam, hphi, p6720_1]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6711, h6719, hc01, hc34, hlam, hphi, ht12, ht23, p6720_1]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6696, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6699, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6711, hlam, p6720_1]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                rcases p6720_3 (m.d 0 1) (by simp) with h6742 | h6742
                                · linarith only [h6742, hlam, p6720_0]
                                · rcases p6720_3 (m.d 1 2) (by simp) with h6744 | h6744
                                  · rcases p6720_3 (m.d 1 3) (by simp) with h6745 | h6745
                                    · linarith only [h6699, h6745, hlam]
                                    · linarith only [h3473, h6745, hlam]
                                  · linarith only [h0, h6744, hlam]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6697, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h3473, hc01, hc14, hlam, hphi, p6720_1]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h0, h4335, h6696, h6699, h6711, hc01, hc34, hlam, hphi, ht12, ht23, p6720_1]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                rcases p6720_3 (m.d 0 1) (by simp) with h6753 | h6753
                                · linarith only [h6753, hlam, p6720_0]
                                · rcases p6720_3 (m.d 1 2) (by simp) with h6755 | h6755
                                  · rcases p6720_3 (m.d 1 3) (by simp) with h6756 | h6756
                                    · linarith only [h6711, h6756, hlam]
                                    · linarith only [h3473, h6756, hlam]
                                  · linarith only [h0, h6755, hlam]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6698, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h0, h4335, h6696, hc01, hc15, hlam, hphi, p6720_1]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [h6713, hlam, p6720_0]
                              · have p6720_0 := h6720c.1
                                have p6720_1 := h6720c.2.1
                                have p6720_2 := h6720c.2.2.1
                                have p6720_3 := h6720c.2.2.2
                                linarith only [hlam, p6720_0]
                            · linarith only [h4044, h6194, h6695, h6699, h6719, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h6194, h6695, h6718, hlam]
                    · linarith only [h6194, h6695, h6697, h6713, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h6194, h6695, h6697, h6698, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h0, h4335, h6696, h6697, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6769 | h6769
            · linarith only [h6194, h6695, h6696, h6769, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6771 | h6771
              · linarith only [h0, h6309, h6696, h6771, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6773 | h6773
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6774 | h6774
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6775 | h6775
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6776 | h6776
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6777 | h6777
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6778 | h6778
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6779 | h6779
                            · rcases h1bigk with h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c | h6780c
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h0, hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h3473, hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h4044, hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h4238, hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h6771, h6776, h6778, hc01, hc23, hlam, hphi, ht12, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h6696, hlam, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h6769, hlam, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h6771, hlam, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                rcases p6780_3 (m.d 0 1) (by simp) with h6791 | h6791
                                · linarith only [h6791, hlam, p6780_0]
                                · rcases p6780_3 (m.d 1 2) (by simp) with h6793 | h6793
                                  · linarith only [h6696, h6793, hlam]
                                  · linarith only [h0, h6793, hlam]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h4044, hc01, hc13, hlam, hphi, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h4238, h6696, hc01, hc23, hlam, hphi, ht12, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                rcases p6780_3 (m.d 0 1) (by simp) with h6800 | h6800
                                · linarith only [h6800, hlam, p6780_0]
                                · rcases p6780_3 (m.d 1 2) (by simp) with h6802 | h6802
                                  · linarith only [h6769, h6802, hlam]
                                  · linarith only [h0, h6802, hlam]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h6773, hlam, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h0, h4335, h6374, h6769, h6774, h6776, hc01, hc23, hlam, hphi, ht12, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                rcases p6780_3 (m.d 0 1) (by simp) with h6809 | h6809
                                · linarith only [h6809, hlam, p6780_0]
                                · rcases p6780_3 (m.d 1 2) (by simp) with h6811 | h6811
                                  · linarith only [h6771, h6811, hlam]
                                  · linarith only [h0, h6811, hlam]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p6780_1]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h6774, hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [h6775, hlam, p6780_0]
                              · have p6780_0 := h6780c.1
                                have p6780_1 := h6780c.2.1
                                have p6780_2 := h6780c.2.2.1
                                have p6780_3 := h6780c.2.2.2
                                linarith only [hlam, p6780_0]
                            · linarith only [h6374, h6695, h6779, hlam]
                          · linarith only [h4044, h6695, h6769, h6778, hlam]
                        · linarith only [h0, h6696, h6777, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4335, h6374, h6696, h6774, h6776, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4044, h6695, h6775, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6823 | h6823
                    · linarith only [h6773, h6774, h6823, hlam]
                    · linarith only [h4044, h6695, h6823, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6826 | h6826
                  · linarith only [h0, h4335, h6374, h6773, h6826, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6828 | h6828
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6829 | h6829
                      · linarith only [h3473, h6773, h6829, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h6696, h6829, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4044, h6695, h6828, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6833 | h6833
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6834 | h6834
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6835 | h6835
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6836 | h6836
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6837 | h6837
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6838 | h6838
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6839 | h6839
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6840 | h6840
                        · linarith only [h0, h4335, h6374, h6833, h6840, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h4335, h6837, h6840, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h4335, h6833, h6836, h6839, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6844 | h6844
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6845 | h6845
                        · linarith only [h0, h4335, h6374, h6833, h6845, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h4335, h6833, h6837, h6845, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h4335, h6833, h6836, h6844, hc01, hc12, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6849 | h6849
                    · linarith only [h6695, h6836, h6837, h6849, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6851 | h6851
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6852 | h6852
                        · linarith only [h3473, h6837, h6852, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6854 | h6854
                          · linarith only [h4044, h6849, h6854, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6856 | h6856
                            · linarith only [h0, h6194, h6833, h6834, h6849, h6851, h6856, hc01, hc13, hlam, hphi]
                            · linarith only [h6833, h6837, h6851, h6856, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h6836, h6837, h6851, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6860 | h6860
                  · linarith only [h0, h4335, h6374, h6836, h6860, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6862 | h6862
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6863 | h6863
                      · linarith only [h6695, h6836, h6862, h6863, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6865 | h6865
                        · linarith only [h4238, h6833, h6860, h6865, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6867 | h6867
                          · linarith only [h6695, h6834, h6867, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h6194, h6862, h6867, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6870 | h6870
                      · linarith only [h6833, h6836, h6862, h6870, hc45, hlam, hphi, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6872 | h6872
                        · linarith only [h0, h4335, h6374, h6833, h6836, h6862, h6872, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6874 | h6874
                          · linarith only [h0, h4335, h6833, h6836, h6862, h6874, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6876 | h6876
                            · linarith only [h0, h4335, h6833, h6836, h6862, h6876, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h4335, h6833, h6836, h6876, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h4335, h6833, h6835, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h4335, h6833, h6834, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6881 | h6881
            · linarith only [h0, h6194, h6833, h6881, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6883 | h6883
              · linarith only [h0, h6309, h6833, h6883, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6885 | h6885
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6886 | h6886
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6887 | h6887
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6888 | h6888
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6889 | h6889
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6890 | h6890
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6891 | h6891
                            · linarith only [h6695, h6833, h6885, h6891, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · rcases h1bigk with h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c | h6893c
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h0, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h3473, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h4044, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h4238, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6883, h6888, h6890, hc01, hc23, hlam, hphi, ht12, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6833, hlam, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6881, hlam, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6883, hlam, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 1) (by simp) with h6904 | h6904
                                · linarith only [h6904, hlam, p6893_0]
                                · rcases p6893_3 (m.d 1 2) (by simp) with h6906 | h6906
                                  · linarith only [h6833, h6906, hlam]
                                  · linarith only [h0, h6906, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h0, h6833, hc01, hc23, hlam, hphi, ht12, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h4044, h6833, hc01, hc23, hlam, hphi, ht12, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h0, h6833, h6883, hc01, hc23, hlam, hphi, ht12, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 1) (by simp) with h6913 | h6913
                                · linarith only [h6913, hlam, p6893_0]
                                · rcases p6893_3 (m.d 1 2) (by simp) with h6915 | h6915
                                  · linarith only [h6881, h6915, hlam]
                                  · linarith only [h0, h6915, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6885, hlam, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6695, h6881, h6887, h6888, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6893_1, u4ehi0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                rcases p6893_3 (m.d 0 1) (by simp) with h6922 | h6922
                                · linarith only [h6922, hlam, p6893_0]
                                · rcases p6893_3 (m.d 1 2) (by simp) with h6924 | h6924
                                  · linarith only [h6883, h6924, hlam]
                                  · linarith only [h0, h6924, hlam]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p6893_1]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6886, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [h6887, hlam, p6893_0]
                              · have p6893_0 := h6893c.1
                                have p6893_1 := h6893c.2.1
                                have p6893_2 := h6893c.2.2.1
                                have p6893_3 := h6893c.2.2.2
                                linarith only [hlam, p6893_0]
                          · linarith only [h0, h6881, h6890, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h6695, h6833, h6885, h6887, h6889, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · linarith only [h6695, h6833, h6885, h6887, h6888, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6934 | h6934
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6935 | h6935
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6936 | h6936
                          · linarith only [h0, h6881, h6887, h6934, h6936, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h6881, h6936, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h6833, h6886, h6935, hlam]
                      · linarith only [h6374, h6833, h6886, h6934, hc03, hc34, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6941 | h6941
                    · linarith only [h6695, h6885, h6886, h6941, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6943 | h6943
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6944 | h6944
                        · linarith only [h6885, h6886, h6944, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h6833, h6944, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h6833, h6885, h6943, hc01, hc13, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6948 | h6948
                  · linarith only [h0, h4335, h6374, h6885, h6948, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6950 | h6950
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6951 | h6951
                      · linarith only [h3473, h6885, h6951, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h6833, h6951, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6954 | h6954
                      · linarith only [h0, h6833, h6885, h6954, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h6833, h6954, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5244000 in
set_option maxHeartbeats 5244000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg4238 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  have h4238 := hg4238
  rcases m.htr 0 2 3 (by decide) (by decide) with h4335 | h4335
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x0 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7_x1 m hb1 hb2 hb4 hb5 hg0 hg3473 hg4044 hg4238 h4335

set_option maxHeartbeats 5438000 in
set_option maxHeartbeats 5438000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s6 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg4044 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  have h4044 := hg4044
  rcases m.htr 0 1 5 (by decide) (by decide) with h4238 | h4238
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4239 | h4239
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4240 | h4240
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4241 | h4241
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4242 | h4242
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4243 | h4243
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4244 | h4244
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4245 | h4245
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4246 | h4246
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4247 | h4247
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4248 | h4248
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4249 | h4249
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4250 | h4250
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4251 | h4251
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4252 | h4252
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4253 | h4253
                                · linarith only [h4239, h4250, h4253, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h4044, h4238, h4246, h4247, h4252, h4253, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h4044, h4238, h4244, h4247, h4249, h4252, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h4044, h4238, h4244, h4247, h4248, h4250, h4251, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4258 | h4258
                            · linarith only [h4244, h4247, h4250, h4258, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4260 | h4260
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4261 | h4261
                                · rcases h1bigk with h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c | h4262c
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h0, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h3473, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4044, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4044, h4244, h4247, hc12, hlam, hphi, ht01, ht0b, ht5b, p4262_1, u5ehi1]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4238, h4248, h4258, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4262_1]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4247, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4262_1, u4ehi3]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4044, h4238, h4248, h4258, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4262_1]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    rcases p4262_3 (m.d 0 1) (by simp) with h4272 | h4272
                                    · linarith only [h0, h4272, hlam]
                                    · linarith only [h4238, h4272, hlam]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4238, h4248, h4258, h4260, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4262_1, u4ehi4]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4244, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4044, h4238, h4244, h4248, h4258, h4260, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4262_1, u4ehi4]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    rcases p4262_3 (m.d 0 1) (by simp) with h4279 | h4279
                                    · linarith only [h3473, h4279, hlam]
                                    · linarith only [h4238, h4279, hlam]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4238, h4248, h4258, h4260, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p4262_1, u4ehi4]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4245, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4247, hlam, p4262_1]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    rcases p4262_3 (m.d 0 1) (by simp) with h4286 | h4286
                                    · linarith only [h4044, h4286, hlam]
                                    · linarith only [h4238, h4286, hlam]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4238, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4246, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4248, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [h4249, hlam, p4262_0]
                                  · have p4262_0 := h4262c.1
                                    have p4262_1 := h4262c.2.1
                                    have p4262_2 := h4262c.2.2.1
                                    have p4262_3 := h4262c.2.2.2
                                    linarith only [hlam, p4262_0]
                                · linarith only [h4250, h4260, h4261, hlam]
                              · linarith only [h0, h4238, h4249, h4260, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h4044, h4238, h4249, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h4044, h4238, h4246, h4247, h4248, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h3473, h4238, h4246, h4247, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h4238, h4246, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h3473, h4238, h4244, h4245, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h4238, h4244, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h4044, h4238, h4243, hlam]
          · linarith only [h3473, h4238, h4242, hlam]
        · linarith only [h3473, h4238, h4239, h4241, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4305 | h4305
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4306 | h4306
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4307 | h4307
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4308 | h4308
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4309 | h4309
                · linarith only [h3473, h4238, h4239, h4240, h4309, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h4238, h4309, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h4238, h4239, h4308, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
            · linarith only [h0, h4238, h4240, h4307, hlam]
          · linarith only [h3473, h4238, h4306, hlam]
        · linarith only [h3473, h4238, h4239, h4305, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4316 | h4316
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4317 | h4317
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4318 | h4318
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4319 | h4319
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4320 | h4320
              · linarith only [h4239, h4316, h4319, h4320, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h0, h4238, h4320, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h4044, h4238, h4319, hlam]
          · linarith only [h4044, h4238, h4239, h4316, h4318, hlam]
        · linarith only [h4044, h4238, h4316, h4317, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4326 | h4326
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4327 | h4327
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4328 | h4328
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4329 | h4329
              · linarith only [h4239, h4326, h4329, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h4238, h4329, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h4044, h4238, h4328, hlam]
          · linarith only [h3473, h4238, h4327, hlam]
        · linarith only [h0, h4238, h4326, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s7 m hb1 hb2 hb4 hb5 h0 h3473 h4044 h4238

end R2N4
