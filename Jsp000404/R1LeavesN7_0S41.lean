import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h25260 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 1 4 5 (by decide) (by decide) with h25261 | h25261
  · rcases m.htr 2 3 4 (by decide) (by decide) with h25262 | h25262
    · rcases m.htr 2 3 5 (by decide) (by decide) with h25263 | h25263
      · rcases m.htr 2 4 5 (by decide) (by decide) with h25264 | h25264
        · rcases m.htr 3 4 5 (by decide) (by decide) with h25265 | h25265
          · rcases h1bigk with h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c | h25266c
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              rcases p25266_3 (m.d 0 1) (by simp) with h25268 | h25268
              · rcases p25266_3 (m.d 1 2) (by simp) with h25269 | h25269
                · linarith only [h25269, hlam, p25266_0]
                · rcases p25266_3 (m.d 1 3) (by simp) with h25271 | h25271
                  · linarith only [h1, h25271, hlam]
                  · linarith only [h23340, h25271, hlam]
              · linarith only [h25268, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              rcases p25266_3 (m.d 0 1) (by simp) with h25275 | h25275
              · rcases p25266_3 (m.d 1 2) (by simp) with h25276 | h25276
                · linarith only [h0, h25276, hlam]
                · rcases p25266_3 (m.d 1 3) (by simp) with h25278 | h25278
                  · linarith only [h25278, hlam, p25266_0]
                  · rcases p25266_3 (m.d 1 4) (by simp) with h25280 | h25280
                    · linarith only [h2, h25280, hlam]
                    · linarith only [h23346, h25280, hlam]
              · linarith only [h25275, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              rcases p25266_3 (m.d 0 1) (by simp) with h25284 | h25284
              · rcases p25266_3 (m.d 1 2) (by simp) with h25285 | h25285
                · linarith only [h0, h25285, hlam]
                · rcases p25266_3 (m.d 1 3) (by simp) with h25287 | h25287
                  · linarith only [h1, h25287, hlam]
                  · rcases p25266_3 (m.d 1 4) (by simp) with h25289 | h25289
                    · linarith only [h25289, hlam, p25266_0]
                    · rcases p25266_3 (m.d 1 5) (by simp) with h25291 | h25291
                      · linarith only [h25291, h3, hlam]
                      · rcases h1emax with h25293 | h25293 | h25293 | h25293 | h25293
                        · linarith only [h1, h25260, h25265, h25293, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases h2bigk with h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c | h25295c
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h22010, hc12, hc25, hlam, hphi, p25295_1]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h4, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h19744, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h22010, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h0, hlam, p25295_1]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h23340, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h23342, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h23344, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            rcases p25295_3 (m.d 0 2) (by simp) with h25306 | h25306
                            · linarith only [h25306, hlam, p25295_0]
                            · rcases p25295_3 (m.d 1 2) (by simp) with h25308 | h25308
                              · linarith only [h23340, h25308, hlam]
                              · rcases p25295_3 (m.d 2 3) (by simp) with h25310 | h25310
                                · rcases p25295_3 (m.d 2 4) (by simp) with h25311 | h25311
                                  · linarith only [h25262, h25311, hlam]
                                  · linarith only [h19744, h25311, hlam]
                                · linarith only [h25310, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            rcases p25295_3 (m.d 0 2) (by simp) with h25315 | h25315
                            · linarith only [h25315, h4, hlam]
                            · linarith only [h0, h25315, hlam]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25295_1]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25295_1]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            rcases p25295_3 (m.d 0 2) (by simp) with h25321 | h25321
                            · linarith only [h25321, hlam, p25295_0]
                            · rcases p25295_3 (m.d 1 2) (by simp) with h25323 | h25323
                              · linarith only [h23342, h25323, hlam]
                              · rcases p25295_3 (m.d 2 3) (by simp) with h25325 | h25325
                                · rcases p25295_3 (m.d 2 4) (by simp) with h25326 | h25326
                                  · rcases p25295_3 (m.d 2 5) (by simp) with h25327 | h25327
                                    · linarith only [h25264, h25327, hlam]
                                    · linarith only [h22010, h25327, hlam]
                                  · linarith only [h25326, hlam, p25295_0]
                                · linarith only [h25325, h4, hlam]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            rcases p25295_3 (m.d 0 2) (by simp) with h25332 | h25332
                            · linarith only [h19744, h25332, hlam]
                            · linarith only [h0, h25332, hlam]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h25262, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h0, h22010, hc12, hc24, hlam, hphi, p25295_1]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            rcases p25295_3 (m.d 0 2) (by simp) with h25338 | h25338
                            · linarith only [h25338, hlam, p25295_0]
                            · rcases p25295_3 (m.d 1 2) (by simp) with h25340 | h25340
                              · linarith only [h23344, h25340, hlam]
                              · rcases p25295_3 (m.d 2 3) (by simp) with h25342 | h25342
                                · rcases p25295_3 (m.d 2 4) (by simp) with h25343 | h25343
                                  · rcases p25295_3 (m.d 2 5) (by simp) with h25344 | h25344
                                    · rcases h4bigk with h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c | h25345c
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        rcases p25345_3 (m.d 0 4) (by simp) with h25347 | h25347
                                        · rcases p25345_3 (m.d 1 4) (by simp) with h25348 | h25348
                                          · linarith only [h2, h25348, hlam]
                                          · rcases p25345_3 (m.d 2 4) (by simp) with h25350 | h25350
                                            · rcases p25345_3 (m.d 3 4) (by simp) with h25351 | h25351
                                              · linarith only [h23337, h25351, hlam]
                                              · linarith only [h23346, h25351, hlam]
                                            · linarith only [h23342, h25350, hlam]
                                        · linarith only [h2, h25347, hlam]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h19744, hlam, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h1, h23337, h23346, h25260, h25265, hc01, hc45, hlam, hphi, ht0b, ht5b, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        rcases p25345_3 (m.d 0 4) (by simp) with h25358 | h25358
                                        · rcases p25345_3 (m.d 1 4) (by simp) with h25359 | h25359
                                          · linarith only [h2, h25359, hlam]
                                          · linarith only [h25261, h25359, hlam]
                                        · linarith only [h25358, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h2, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h23342, hlam, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h23346, hlam, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25266_1, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        rcases p25345_3 (m.d 0 4) (by simp) with h25369 | h25369
                                        · linarith only [h19744, h25369, hlam]
                                        · linarith only [h2, h25369, hlam]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        rcases p25345_3 (m.d 0 4) (by simp) with h25374 | h25374
                                        · linarith only [h19744, h25374, hlam]
                                        · linarith only [h23339, h25374, hlam]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h23337, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25265, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25345_1]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25262, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        rcases p25345_3 (m.d 0 4) (by simp) with h25381 | h25381
                                        · rcases p25345_3 (m.d 1 4) (by simp) with h25382 | h25382
                                          · linarith only [h23346, h25382, hlam]
                                          · linarith only [h25261, h25382, hlam]
                                        · linarith only [h23339, h25381, hlam]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h23339, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25261, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25264, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [h25265, hlam, p25345_0]
                                      · have p25345_0 := h25345c.1
                                        have p25345_1 := h25345c.2.1
                                        have p25345_2 := h25345c.2.2.1
                                        have p25345_3 := h25345c.2.2.2
                                        linarith only [hlam, p25345_0]
                                    · linarith only [h25344, hlam, p25295_0]
                                  · linarith only [h19744, h25343, hlam]
                                · linarith only [h25342, h4, hlam]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            rcases p25295_3 (m.d 0 2) (by simp) with h25394 | h25394
                            · linarith only [h22010, h25394, hlam]
                            · linarith only [h0, h25394, hlam]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h25263, hlam, p25295_0]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [h25264, hlam, p25295_1]
                          · have p25295_0 := h25295c.1
                            have p25295_1 := h25295c.2.1
                            have p25295_2 := h25295c.2.2.1
                            have p25295_3 := h25295c.2.2.2
                            linarith only [hlam, p25295_0]
                        · rcases h2bigk with h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c | h25400c
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p25400_1]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h4, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h19744, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h22010, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h0, hlam, p25400_1]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h23340, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h23342, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h23344, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            rcases p25400_3 (m.d 0 2) (by simp) with h25411 | h25411
                            · linarith only [h25411, hlam, p25400_0]
                            · rcases p25400_3 (m.d 1 2) (by simp) with h25413 | h25413
                              · linarith only [h23340, h25413, hlam]
                              · rcases p25400_3 (m.d 2 3) (by simp) with h25415 | h25415
                                · rcases p25400_3 (m.d 2 4) (by simp) with h25416 | h25416
                                  · linarith only [h25262, h25416, hlam]
                                  · linarith only [h19744, h25416, hlam]
                                · linarith only [h25415, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            rcases p25400_3 (m.d 0 2) (by simp) with h25420 | h25420
                            · linarith only [h25420, h4, hlam]
                            · linarith only [h0, h25420, hlam]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25400_1]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25400_1]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            rcases p25400_3 (m.d 0 2) (by simp) with h25426 | h25426
                            · linarith only [h25426, hlam, p25400_0]
                            · rcases p25400_3 (m.d 1 2) (by simp) with h25428 | h25428
                              · linarith only [h23342, h25428, hlam]
                              · rcases p25400_3 (m.d 2 3) (by simp) with h25430 | h25430
                                · rcases p25400_3 (m.d 2 4) (by simp) with h25431 | h25431
                                  · rcases p25400_3 (m.d 2 5) (by simp) with h25432 | h25432
                                    · linarith only [h25264, h25432, hlam]
                                    · linarith only [h22010, h25432, hlam]
                                  · linarith only [h25431, hlam, p25400_0]
                                · linarith only [h25430, h4, hlam]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            rcases p25400_3 (m.d 0 2) (by simp) with h25437 | h25437
                            · linarith only [h19744, h25437, hlam]
                            · linarith only [h0, h25437, hlam]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h25262, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h0, h22010, hc12, hc24, hlam, hphi, p25400_1]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            rcases p25400_3 (m.d 0 2) (by simp) with h25443 | h25443
                            · linarith only [h25443, hlam, p25400_0]
                            · rcases p25400_3 (m.d 1 2) (by simp) with h25445 | h25445
                              · linarith only [h23344, h25445, hlam]
                              · rcases p25400_3 (m.d 2 3) (by simp) with h25447 | h25447
                                · rcases p25400_3 (m.d 2 4) (by simp) with h25448 | h25448
                                  · rcases p25400_3 (m.d 2 5) (by simp) with h25449 | h25449
                                    · rcases h4bigk with h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c | h25450c
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        rcases p25450_3 (m.d 0 4) (by simp) with h25452 | h25452
                                        · rcases p25450_3 (m.d 1 4) (by simp) with h25453 | h25453
                                          · linarith only [h2, h25453, hlam]
                                          · rcases p25450_3 (m.d 2 4) (by simp) with h25455 | h25455
                                            · rcases p25450_3 (m.d 3 4) (by simp) with h25456 | h25456
                                              · linarith only [h23337, h25456, hlam]
                                              · linarith only [h23346, h25456, hlam]
                                            · linarith only [h23342, h25455, hlam]
                                        · linarith only [h2, h25452, hlam]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h19744, hlam, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h19744, h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        rcases p25450_3 (m.d 0 4) (by simp) with h25463 | h25463
                                        · rcases p25450_3 (m.d 1 4) (by simp) with h25464 | h25464
                                          · linarith only [h2, h25464, hlam]
                                          · linarith only [h25261, h25464, hlam]
                                        · linarith only [h25463, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h2, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h23342, hlam, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h23346, hlam, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25266_1, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        rcases p25450_3 (m.d 0 4) (by simp) with h25474 | h25474
                                        · linarith only [h19744, h25474, hlam]
                                        · linarith only [h2, h25474, hlam]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        rcases p25450_3 (m.d 0 4) (by simp) with h25479 | h25479
                                        · linarith only [h19744, h25479, hlam]
                                        · linarith only [h23339, h25479, hlam]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h23337, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25265, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25450_1]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h25262, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        rcases p25450_3 (m.d 0 4) (by simp) with h25486 | h25486
                                        · rcases p25450_3 (m.d 1 4) (by simp) with h25487 | h25487
                                          · linarith only [h23346, h25487, hlam]
                                          · linarith only [h25261, h25487, hlam]
                                        · linarith only [h23339, h25486, hlam]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h23339, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h25261, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h25264, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [h25265, hlam, p25450_0]
                                      · have p25450_0 := h25450c.1
                                        have p25450_1 := h25450c.2.1
                                        have p25450_2 := h25450c.2.2.1
                                        have p25450_3 := h25450c.2.2.2
                                        linarith only [hlam, p25450_0]
                                    · linarith only [h25449, hlam, p25400_0]
                                  · linarith only [h19744, h25448, hlam]
                                · linarith only [h25447, h4, hlam]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            rcases p25400_3 (m.d 0 2) (by simp) with h25499 | h25499
                            · linarith only [h22010, h25499, hlam]
                            · linarith only [h0, h25499, hlam]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h25263, hlam, p25400_0]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [h25264, hlam, p25400_1]
                          · have p25400_0 := h25400c.1
                            have p25400_1 := h25400c.2.1
                            have p25400_2 := h25400c.2.2.1
                            have p25400_3 := h25400c.2.2.2
                            linarith only [hlam, p25400_0]
                        · rcases h2bigk with h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c | h25505c
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p25505_1]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h4, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h19744, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h22010, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h0, hlam, p25505_1]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h23340, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h23342, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h23344, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            rcases p25505_3 (m.d 0 2) (by simp) with h25516 | h25516
                            · linarith only [h25516, hlam, p25505_0]
                            · rcases p25505_3 (m.d 1 2) (by simp) with h25518 | h25518
                              · linarith only [h23340, h25518, hlam]
                              · rcases p25505_3 (m.d 2 3) (by simp) with h25520 | h25520
                                · rcases p25505_3 (m.d 2 4) (by simp) with h25521 | h25521
                                  · linarith only [h25262, h25521, hlam]
                                  · linarith only [h19744, h25521, hlam]
                                · linarith only [h25520, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            rcases p25505_3 (m.d 0 2) (by simp) with h25525 | h25525
                            · linarith only [h25525, h4, hlam]
                            · linarith only [h0, h25525, hlam]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25505_1]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25505_1]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            rcases p25505_3 (m.d 0 2) (by simp) with h25531 | h25531
                            · linarith only [h25531, hlam, p25505_0]
                            · rcases p25505_3 (m.d 1 2) (by simp) with h25533 | h25533
                              · linarith only [h23342, h25533, hlam]
                              · rcases p25505_3 (m.d 2 3) (by simp) with h25535 | h25535
                                · rcases p25505_3 (m.d 2 4) (by simp) with h25536 | h25536
                                  · rcases p25505_3 (m.d 2 5) (by simp) with h25537 | h25537
                                    · linarith only [h25264, h25537, hlam]
                                    · linarith only [h22010, h25537, hlam]
                                  · linarith only [h25536, hlam, p25505_0]
                                · linarith only [h25535, h4, hlam]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            rcases p25505_3 (m.d 0 2) (by simp) with h25542 | h25542
                            · linarith only [h19744, h25542, hlam]
                            · linarith only [h0, h25542, hlam]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h25262, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h0, h22010, hc12, hc24, hlam, hphi, p25505_1]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            rcases p25505_3 (m.d 0 2) (by simp) with h25548 | h25548
                            · linarith only [h25548, hlam, p25505_0]
                            · rcases p25505_3 (m.d 1 2) (by simp) with h25550 | h25550
                              · linarith only [h23344, h25550, hlam]
                              · rcases p25505_3 (m.d 2 3) (by simp) with h25552 | h25552
                                · rcases p25505_3 (m.d 2 4) (by simp) with h25553 | h25553
                                  · rcases p25505_3 (m.d 2 5) (by simp) with h25554 | h25554
                                    · rcases h4bigk with h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c | h25555c
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        rcases p25555_3 (m.d 0 4) (by simp) with h25557 | h25557
                                        · rcases p25555_3 (m.d 1 4) (by simp) with h25558 | h25558
                                          · linarith only [h2, h25558, hlam]
                                          · rcases p25555_3 (m.d 2 4) (by simp) with h25560 | h25560
                                            · rcases p25555_3 (m.d 3 4) (by simp) with h25561 | h25561
                                              · linarith only [h23337, h25561, hlam]
                                              · linarith only [h23346, h25561, hlam]
                                            · linarith only [h23342, h25560, hlam]
                                        · linarith only [h2, h25557, hlam]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h19744, hlam, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h19744, h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        rcases p25555_3 (m.d 0 4) (by simp) with h25568 | h25568
                                        · rcases p25555_3 (m.d 1 4) (by simp) with h25569 | h25569
                                          · linarith only [h2, h25569, hlam]
                                          · linarith only [h25261, h25569, hlam]
                                        · linarith only [h25568, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h2, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h23342, hlam, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h23346, hlam, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25266_1, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        rcases p25555_3 (m.d 0 4) (by simp) with h25579 | h25579
                                        · linarith only [h19744, h25579, hlam]
                                        · linarith only [h2, h25579, hlam]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        rcases p25555_3 (m.d 0 4) (by simp) with h25584 | h25584
                                        · linarith only [h19744, h25584, hlam]
                                        · linarith only [h23339, h25584, hlam]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h23337, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25265, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25555_1]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h25262, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        rcases p25555_3 (m.d 0 4) (by simp) with h25591 | h25591
                                        · rcases p25555_3 (m.d 1 4) (by simp) with h25592 | h25592
                                          · linarith only [h23346, h25592, hlam]
                                          · linarith only [h25261, h25592, hlam]
                                        · linarith only [h23339, h25591, hlam]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h23339, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h25261, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h25264, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [h25265, hlam, p25555_0]
                                      · have p25555_0 := h25555c.1
                                        have p25555_1 := h25555c.2.1
                                        have p25555_2 := h25555c.2.2.1
                                        have p25555_3 := h25555c.2.2.2
                                        linarith only [hlam, p25555_0]
                                    · linarith only [h25554, hlam, p25505_0]
                                  · linarith only [h19744, h25553, hlam]
                                · linarith only [h25552, h4, hlam]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            rcases p25505_3 (m.d 0 2) (by simp) with h25604 | h25604
                            · linarith only [h22010, h25604, hlam]
                            · linarith only [h0, h25604, hlam]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h25263, hlam, p25505_0]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [h25264, hlam, p25505_1]
                          · have p25505_0 := h25505c.1
                            have p25505_1 := h25505c.2.1
                            have p25505_2 := h25505c.2.2.1
                            have p25505_3 := h25505c.2.2.2
                            linarith only [hlam, p25505_0]
                        · rcases h2bigk with h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c | h25610c
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p25610_1]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h4, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h19744, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h22010, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h0, hlam, p25610_1]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h23340, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h23342, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h23344, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            rcases p25610_3 (m.d 0 2) (by simp) with h25621 | h25621
                            · linarith only [h25621, hlam, p25610_0]
                            · rcases p25610_3 (m.d 1 2) (by simp) with h25623 | h25623
                              · linarith only [h23340, h25623, hlam]
                              · rcases p25610_3 (m.d 2 3) (by simp) with h25625 | h25625
                                · rcases p25610_3 (m.d 2 4) (by simp) with h25626 | h25626
                                  · linarith only [h25262, h25626, hlam]
                                  · linarith only [h19744, h25626, hlam]
                                · linarith only [h25625, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            rcases p25610_3 (m.d 0 2) (by simp) with h25630 | h25630
                            · linarith only [h25630, h4, hlam]
                            · linarith only [h0, h25630, hlam]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25610_1]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25610_1]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            rcases p25610_3 (m.d 0 2) (by simp) with h25636 | h25636
                            · linarith only [h25636, hlam, p25610_0]
                            · rcases p25610_3 (m.d 1 2) (by simp) with h25638 | h25638
                              · linarith only [h23342, h25638, hlam]
                              · rcases p25610_3 (m.d 2 3) (by simp) with h25640 | h25640
                                · rcases p25610_3 (m.d 2 4) (by simp) with h25641 | h25641
                                  · rcases p25610_3 (m.d 2 5) (by simp) with h25642 | h25642
                                    · linarith only [h25264, h25642, hlam]
                                    · linarith only [h22010, h25642, hlam]
                                  · linarith only [h25641, hlam, p25610_0]
                                · linarith only [h25640, h4, hlam]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            rcases p25610_3 (m.d 0 2) (by simp) with h25647 | h25647
                            · linarith only [h19744, h25647, hlam]
                            · linarith only [h0, h25647, hlam]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h25262, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h0, h22010, hc12, hc24, hlam, hphi, p25610_1]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            rcases p25610_3 (m.d 0 2) (by simp) with h25653 | h25653
                            · linarith only [h25653, hlam, p25610_0]
                            · rcases p25610_3 (m.d 1 2) (by simp) with h25655 | h25655
                              · linarith only [h23344, h25655, hlam]
                              · rcases p25610_3 (m.d 2 3) (by simp) with h25657 | h25657
                                · rcases p25610_3 (m.d 2 4) (by simp) with h25658 | h25658
                                  · rcases p25610_3 (m.d 2 5) (by simp) with h25659 | h25659
                                    · rcases h4bigk with h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c | h25660c
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        rcases p25660_3 (m.d 0 4) (by simp) with h25662 | h25662
                                        · rcases p25660_3 (m.d 1 4) (by simp) with h25663 | h25663
                                          · linarith only [h2, h25663, hlam]
                                          · rcases p25660_3 (m.d 2 4) (by simp) with h25665 | h25665
                                            · rcases p25660_3 (m.d 3 4) (by simp) with h25666 | h25666
                                              · linarith only [h23337, h25666, hlam]
                                              · linarith only [h23346, h25666, hlam]
                                            · linarith only [h23342, h25665, hlam]
                                        · linarith only [h2, h25662, hlam]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h19744, hlam, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23346, h25260, h25265, hc04, hc45, hlam, hphi, ht0b, ht5b, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        rcases p25660_3 (m.d 0 4) (by simp) with h25673 | h25673
                                        · rcases p25660_3 (m.d 1 4) (by simp) with h25674 | h25674
                                          · linarith only [h2, h25674, hlam]
                                          · linarith only [h25261, h25674, hlam]
                                        · linarith only [h25673, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h2, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23342, hlam, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23346, hlam, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25266_1, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        rcases p25660_3 (m.d 0 4) (by simp) with h25684 | h25684
                                        · linarith only [h19744, h25684, hlam]
                                        · linarith only [h2, h25684, hlam]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23346, h25260, h25262, h25265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        rcases p25660_3 (m.d 0 4) (by simp) with h25689 | h25689
                                        · linarith only [h19744, h25689, hlam]
                                        · linarith only [h23339, h25689, hlam]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23337, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23337, h23346, h25260, h25265, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25660_1]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h25262, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        rcases p25660_3 (m.d 0 4) (by simp) with h25696 | h25696
                                        · rcases p25660_3 (m.d 1 4) (by simp) with h25697 | h25697
                                          · linarith only [h23346, h25697, hlam]
                                          · linarith only [h25261, h25697, hlam]
                                        · linarith only [h23339, h25696, hlam]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h23339, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h25261, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h25264, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [h25265, hlam, p25660_0]
                                      · have p25660_0 := h25660c.1
                                        have p25660_1 := h25660c.2.1
                                        have p25660_2 := h25660c.2.2.1
                                        have p25660_3 := h25660c.2.2.2
                                        linarith only [hlam, p25660_0]
                                    · linarith only [h25659, hlam, p25610_0]
                                  · linarith only [h19744, h25658, hlam]
                                · linarith only [h25657, h4, hlam]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            rcases p25610_3 (m.d 0 2) (by simp) with h25709 | h25709
                            · linarith only [h22010, h25709, hlam]
                            · linarith only [h0, h25709, hlam]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h25263, hlam, p25610_0]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [h25264, hlam, p25610_1]
                          · have p25610_0 := h25610c.1
                            have p25610_1 := h25610c.2.1
                            have p25610_2 := h25610c.2.2.1
                            have p25610_3 := h25610c.2.2.2
                            linarith only [hlam, p25610_0]
              · linarith only [h25284, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              rcases p25266_3 (m.d 0 1) (by simp) with h25716 | h25716
              · rcases p25266_3 (m.d 1 2) (by simp) with h25717 | h25717
                · linarith only [h0, h25717, hlam]
                · rcases p25266_3 (m.d 1 3) (by simp) with h25719 | h25719
                  · linarith only [h1, h25719, hlam]
                  · linarith only [h25260, h25719, hlam]
              · linarith only [h25716, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h0, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23340, hlam, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23342, hlam, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23344, hlam, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h1, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23337, h23346, h4, hc12, hc23, hlam, hphi, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23346, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23337, h23344, h23346, h4, hc12, hc23, hlam, hphi, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h2, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23337, h23346, h4, hc12, hc23, hlam, hphi, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23337, h23340, h23346, h4, hc12, hc23, hlam, hphi, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23337, h23344, h23346, h4, hc12, hc23, hlam, hphi, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h3, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h23337, h23346, h25260, h4, hc12, hc23, hlam, hphi, p25266_1]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h25260, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [h25261, hlam, p25266_0]
            · have p25266_0 := h25266c.1
              have p25266_1 := h25266c.2.1
              have p25266_2 := h25266c.2.2.1
              have p25266_3 := h25266c.2.2.2
              linarith only [hlam, p25266_0]
          · linarith only [h23337, h23339, h23340, h23346, h25265, h4, hc12, hc23, hlam, hphi]
        · linarith only [h0, h19744, h23337, h23346, h25260, h25261, h25264, h4, hc12, hc23, hlam, hphi]
      · linarith only [h23337, h23346, h25263, h4, hc13, hc35, hlam, hphi]
    · linarith only [h23337, h25262, h4, hlam]
  · linarith only [h23346, h25260, h25261, hlam]

end R2N4
