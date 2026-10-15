import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h9272 | h9272
  · rcases m.htr 1 4 5 (by decide) (by decide) with h9273 | h9273
    · linarith only [h2, h9, h9273, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h9275 | h9275
      · rcases m.htr 2 3 5 (by decide) (by decide) with h9276 | h9276
        · rcases m.htr 2 4 5 (by decide) (by decide) with h9277 | h9277
          · linarith only [h2, h9, h9269, h9277, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h9279 | h9279
            · linarith only [h9, h9268, h9275, h9279, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases h1bigk with h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c | h9281c
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h9268, h9276, h9279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9281_1]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9284 | h9284
                · rcases p9281_3 (m.d 1 2) (by simp) with h9285 | h9285
                  · linarith only [h0, h9285, hlam]
                  · linarith only [h9268, h9285, hlam]
                · linarith only [h9284, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9289 | h9289
                · rcases p9281_3 (m.d 1 2) (by simp) with h9290 | h9290
                  · linarith only [h0, h9290, hlam]
                  · linarith only [h9269, h9290, hlam]
                · linarith only [h9289, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9294 | h9294
                · rcases p9281_3 (m.d 1 2) (by simp) with h9295 | h9295
                  · linarith only [h0, h9295, hlam]
                  · linarith only [h9270, h9295, hlam]
                · linarith only [h9294, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h0, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h0, h9268, h9276, h9279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9281_1]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9302 | h9302
                · rcases p9281_3 (m.d 1 2) (by simp) with h9303 | h9303
                  · rcases p9281_3 (m.d 1 3) (by simp) with h9304 | h9304
                    · linarith only [h9268, h9304, hlam]
                    · linarith only [h9271, h9304, hlam]
                  · linarith only [h9269, h9303, hlam]
                · linarith only [h2, h9302, hlam]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9309 | h9309
                · rcases p9281_3 (m.d 1 2) (by simp) with h9310 | h9310
                  · rcases p9281_3 (m.d 1 3) (by simp) with h9311 | h9311
                    · linarith only [h9268, h9311, hlam]
                    · linarith only [h9272, h9311, hlam]
                  · linarith only [h9270, h9310, hlam]
                · linarith only [h3, h9309, hlam]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h1, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h9268, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9319 | h9319
                · rcases p9281_3 (m.d 1 2) (by simp) with h9320 | h9320
                  · rcases p9281_3 (m.d 1 3) (by simp) with h9321 | h9321
                    · rcases p9281_3 (m.d 1 4) (by simp) with h9322 | h9322
                      · linarith only [h9271, h9322, hlam]
                      · rcases p9281_3 (m.d 1 5) (by simp) with h9324 | h9324
                        · linarith only [h9272, h9324, hlam]
                        · linarith only [h9273, h9324, hlam]
                    · linarith only [h9271, h9321, hlam]
                  · linarith only [h9269, h9320, hlam]
                · linarith only [h2, h9319, hlam]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9330 | h9330
                · rcases p9281_3 (m.d 1 2) (by simp) with h9331 | h9331
                  · rcases p9281_3 (m.d 1 3) (by simp) with h9332 | h9332
                    · rcases p9281_3 (m.d 1 4) (by simp) with h9333 | h9333
                      · linarith only [h9271, h9333, hlam]
                      · rcases p9281_3 (m.d 1 5) (by simp) with h9335 | h9335
                        · linarith only [h9272, h9335, hlam]
                        · rcases h1emax with h9337 | h9337 | h9337 | h9337 | h9337
                          · linarith only [h0, h9268, h9273, h9337, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                          · linarith only [h9268, h9269, h9273, h9275, h9337, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                          · linarith only [h9269, h9273, h9275, h9337, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                          · rcases h2bigk with h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c | h9341c
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h0, h9268, h9269, h9273, h9275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9281_1, p9341_1]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              rcases p9341_3 (m.d 0 2) (by simp) with h9344 | h9344
                              · rcases p9341_3 (m.d 1 2) (by simp) with h9345 | h9345
                                · linarith only [h0, h9345, hlam]
                                · linarith only [h9268, h9345, hlam]
                              · linarith only [h9344, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              rcases p9341_3 (m.d 0 2) (by simp) with h9349 | h9349
                              · rcases p9341_3 (m.d 1 2) (by simp) with h9350 | h9350
                                · linarith only [h0, h9350, hlam]
                                · linarith only [h9269, h9350, hlam]
                              · linarith only [h9349, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              rcases p9341_3 (m.d 0 2) (by simp) with h9354 | h9354
                              · rcases p9341_3 (m.d 1 2) (by simp) with h9355 | h9355
                                · linarith only [h0, h9355, hlam]
                                · linarith only [h9270, h9355, hlam]
                              · linarith only [h9354, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h0, hlam, p9341_1]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h0, h9276, h9279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9341_1]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              rcases p9341_3 (m.d 0 2) (by simp) with h9362 | h9362
                              · rcases p9341_3 (m.d 1 2) (by simp) with h9363 | h9363
                                · rcases p9341_3 (m.d 2 3) (by simp) with h9364 | h9364
                                  · linarith only [h9268, h9364, hlam]
                                  · linarith only [h9275, h9364, hlam]
                                · linarith only [h9363, hlam, p9341_0]
                              · linarith only [h5, h9362, hlam]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              rcases p9341_3 (m.d 0 2) (by simp) with h9369 | h9369
                              · rcases p9341_3 (m.d 1 2) (by simp) with h9370 | h9370
                                · rcases p9341_3 (m.d 2 3) (by simp) with h9371 | h9371
                                  · linarith only [h9268, h9371, hlam]
                                  · linarith only [h9276, h9371, hlam]
                                · linarith only [h9370, hlam, p9341_0]
                              · linarith only [h6, h9369, hlam]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h4, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h9268, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h0, h9268, h9275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9341_1]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h0, h9268, hc01, hc25, hlam, hphi, ht0b, ht5b, p9341_1]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h5, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h9269, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h9275, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h9277, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h6, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h9270, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h9276, hlam, p9341_0]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [h0, h9270, h9275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9341_1]
                            · have p9341_0 := h9341c.1
                              have p9341_1 := h9341c.2.1
                              have p9341_2 := h9341c.2.2.1
                              have p9341_3 := h9341c.2.2.2
                              linarith only [hlam, p9341_0]
                          · rcases h2bigk with h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c | h9391c
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h9268, hc02, hc15, hlam, hphi, ht0b, ht5b, p9281_1, p9391_1]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              rcases p9391_3 (m.d 0 2) (by simp) with h9394 | h9394
                              · rcases p9391_3 (m.d 1 2) (by simp) with h9395 | h9395
                                · linarith only [h0, h9395, hlam]
                                · linarith only [h9268, h9395, hlam]
                              · linarith only [h9394, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              rcases p9391_3 (m.d 0 2) (by simp) with h9399 | h9399
                              · rcases p9391_3 (m.d 1 2) (by simp) with h9400 | h9400
                                · linarith only [h0, h9400, hlam]
                                · linarith only [h9269, h9400, hlam]
                              · linarith only [h9399, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              rcases p9391_3 (m.d 0 2) (by simp) with h9404 | h9404
                              · rcases p9391_3 (m.d 1 2) (by simp) with h9405 | h9405
                                · linarith only [h0, h9405, hlam]
                                · linarith only [h9270, h9405, hlam]
                              · linarith only [h9404, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h0, hlam, p9391_1]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h0, h9276, h9279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9391_1]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              rcases p9391_3 (m.d 0 2) (by simp) with h9412 | h9412
                              · rcases p9391_3 (m.d 1 2) (by simp) with h9413 | h9413
                                · rcases p9391_3 (m.d 2 3) (by simp) with h9414 | h9414
                                  · linarith only [h9268, h9414, hlam]
                                  · linarith only [h9275, h9414, hlam]
                                · linarith only [h9413, hlam, p9391_0]
                              · linarith only [h5, h9412, hlam]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              rcases p9391_3 (m.d 0 2) (by simp) with h9419 | h9419
                              · rcases p9391_3 (m.d 1 2) (by simp) with h9420 | h9420
                                · rcases p9391_3 (m.d 2 3) (by simp) with h9421 | h9421
                                  · linarith only [h9268, h9421, hlam]
                                  · linarith only [h9276, h9421, hlam]
                                · linarith only [h9420, hlam, p9391_0]
                              · linarith only [h6, h9419, hlam]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h4, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h9268, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h0, h9268, h9275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9391_1]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h0, h9268, h9276, h9279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9391_1]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h5, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h9269, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h9275, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h9277, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h6, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h9270, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h9276, hlam, p9391_0]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [h0, h9270, h9275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9391_1]
                            · have p9391_0 := h9391c.1
                              have p9391_1 := h9391c.2.1
                              have p9391_2 := h9391c.2.2.1
                              have p9391_3 := h9391c.2.2.2
                              linarith only [hlam, p9391_0]
                    · linarith only [h9272, h9332, hlam]
                  · linarith only [h9270, h9331, hlam]
                · linarith only [h3, h9330, hlam]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h2, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h9269, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h9271, hlam, p9281_1]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h9273, hlam, p9281_1]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h3, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h9270, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [h9272, hlam, p9281_0]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                rcases p9281_3 (m.d 0 1) (by simp) with h9452 | h9452
                · rcases p9281_3 (m.d 1 2) (by simp) with h9453 | h9453
                  · rcases p9281_3 (m.d 1 3) (by simp) with h9454 | h9454
                    · rcases p9281_3 (m.d 1 4) (by simp) with h9455 | h9455
                      · linarith only [h9273, h9455, hlam]
                      · rcases p9281_3 (m.d 1 5) (by simp) with h9457 | h9457
                        · rcases h1emax with h9458 | h9458 | h9458 | h9458 | h9458
                          · linarith only [h0, h9268, h9458, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h9268, h9269, h9272, h9275, h9458, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                          · linarith only [h9269, h9272, h9275, h9458, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                          · rcases h2bigk with h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c | h9462c
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h9268, h9269, h9272, h9275, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9281_1, p9462_1]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              rcases p9462_3 (m.d 0 2) (by simp) with h9465 | h9465
                              · rcases p9462_3 (m.d 1 2) (by simp) with h9466 | h9466
                                · linarith only [h0, h9466, hlam]
                                · linarith only [h9268, h9466, hlam]
                              · linarith only [h9465, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              rcases p9462_3 (m.d 0 2) (by simp) with h9470 | h9470
                              · rcases p9462_3 (m.d 1 2) (by simp) with h9471 | h9471
                                · linarith only [h0, h9471, hlam]
                                · linarith only [h9269, h9471, hlam]
                              · linarith only [h9470, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              rcases p9462_3 (m.d 0 2) (by simp) with h9475 | h9475
                              · rcases p9462_3 (m.d 1 2) (by simp) with h9476 | h9476
                                · linarith only [h0, h9476, hlam]
                                · linarith only [h9270, h9476, hlam]
                              · linarith only [h9475, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h0, hlam, p9462_1]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h0, h9276, h9279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9462_1]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              rcases p9462_3 (m.d 0 2) (by simp) with h9483 | h9483
                              · rcases p9462_3 (m.d 1 2) (by simp) with h9484 | h9484
                                · rcases p9462_3 (m.d 2 3) (by simp) with h9485 | h9485
                                  · linarith only [h9268, h9485, hlam]
                                  · linarith only [h9275, h9485, hlam]
                                · linarith only [h9484, hlam, p9462_0]
                              · linarith only [h5, h9483, hlam]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              rcases p9462_3 (m.d 0 2) (by simp) with h9490 | h9490
                              · rcases p9462_3 (m.d 1 2) (by simp) with h9491 | h9491
                                · rcases p9462_3 (m.d 2 3) (by simp) with h9492 | h9492
                                  · linarith only [h9268, h9492, hlam]
                                  · linarith only [h9276, h9492, hlam]
                                · linarith only [h9491, hlam, p9462_0]
                              · linarith only [h6, h9490, hlam]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h4, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h9268, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h0, h9268, h9275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9462_1]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h0, h9268, hc01, hc25, hlam, hphi, ht0b, ht5b, p9462_1]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h5, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h9269, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h9275, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h9277, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h6, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h9270, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h9276, hlam, p9462_0]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [h0, h9270, h9275, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9462_1]
                            · have p9462_0 := h9462c.1
                              have p9462_1 := h9462c.2.1
                              have p9462_2 := h9462c.2.2.1
                              have p9462_3 := h9462c.2.2.2
                              linarith only [hlam, p9462_0]
                          · linarith only [h9269, h9275, h9458, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9281_1]
                        · linarith only [h9273, h9457, hlam]
                    · linarith only [h9271, h9454, hlam]
                  · linarith only [h9269, h9453, hlam]
                · linarith only [h2, h9452, hlam]
              · have p9281_0 := h9281c.1
                have p9281_1 := h9281c.2.1
                have p9281_2 := h9281c.2.2.1
                have p9281_3 := h9281c.2.2.2
                linarith only [hlam, p9281_0]
        · linarith only [h0, h9268, h9272, h9275, h9276, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h9519 | h9519
        · linarith only [h0, h9268, h9271, h9275, h9519, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h9521 | h9521
          · linarith only [h5, h9, h9521, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h9523 | h9523
            · linarith only [h2, h9, h9271, h9523, hlam]
            · rcases h1bigk with h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c | h9525c
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9268, h9271, h9275, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9271, h9275, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                rcases p9525_3 (m.d 0 1) (by simp) with h9529 | h9529
                · rcases p9525_3 (m.d 1 2) (by simp) with h9530 | h9530
                  · linarith only [h0, h9530, hlam]
                  · linarith only [h9269, h9530, hlam]
                · linarith only [h9529, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                rcases p9525_3 (m.d 0 1) (by simp) with h9534 | h9534
                · rcases p9525_3 (m.d 1 2) (by simp) with h9535 | h9535
                  · linarith only [h0, h9535, hlam]
                  · linarith only [h9270, h9535, hlam]
                · linarith only [h9534, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h0, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9272, h9275, h9523, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h0, h9271, h9275, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h0, h9271, h9273, h9275, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h1, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9268, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h1, h9271, h9275, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h0, h9268, h9271, h9273, h9275, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h2, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9269, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9271, hlam, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9273, hlam, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h3, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9270, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h9272, hlam, p9525_0]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [h3, h9271, h9275, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9525_1]
              · have p9525_0 := h9525c.1
                have p9525_1 := h9525c.2.1
                have p9525_2 := h9525c.2.2.1
                have p9525_3 := h9525c.2.2.2
                linarith only [hlam, p9525_0]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h9559 | h9559
    · linarith only [h2, h8, h9, h9271, h9272, h9559, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h9561 | h9561
      · rcases m.htr 2 3 5 (by decide) (by decide) with h9562 | h9562
        · linarith only [h9268, h9272, h9562, hlam]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h9564 | h9564
          · linarith only [h2, h9, h9269, h9564, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h9566 | h9566
            · linarith only [h0, h2, h4, h9, h9561, h9566, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h1bigk with h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c | h9568c
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h9268, h9561, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                rcases p9568_3 (m.d 0 1) (by simp) with h9571 | h9571
                · rcases p9568_3 (m.d 1 2) (by simp) with h9572 | h9572
                  · linarith only [h0, h9572, hlam]
                  · linarith only [h9268, h9572, hlam]
                · linarith only [h9571, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                rcases p9568_3 (m.d 0 1) (by simp) with h9576 | h9576
                · rcases p9568_3 (m.d 1 2) (by simp) with h9577 | h9577
                  · linarith only [h0, h9577, hlam]
                  · linarith only [h9269, h9577, hlam]
                · linarith only [h9576, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                rcases p9568_3 (m.d 0 1) (by simp) with h9581 | h9581
                · rcases p9568_3 (m.d 1 2) (by simp) with h9582 | h9582
                  · linarith only [h0, h9582, hlam]
                  · linarith only [h9270, h9582, hlam]
                · linarith only [h9581, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h0, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h0, h9268, h9561, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                rcases p9568_3 (m.d 0 1) (by simp) with h9589 | h9589
                · rcases p9568_3 (m.d 1 2) (by simp) with h9590 | h9590
                  · rcases p9568_3 (m.d 1 3) (by simp) with h9591 | h9591
                    · linarith only [h9268, h9591, hlam]
                    · linarith only [h9271, h9591, hlam]
                  · linarith only [h9269, h9590, hlam]
                · linarith only [h2, h9589, hlam]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h0, h9270, h9561, h9562, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h1, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h9268, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h0, h4, h8, h9272, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h9272, hlam, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h2, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h9269, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h9271, hlam, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h9559, hlam, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h3, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h9270, hlam, p9568_0]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [h3, h9268, h9561, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9568_1]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                rcases p9568_3 (m.d 0 1) (by simp) with h9610 | h9610
                · rcases p9568_3 (m.d 1 2) (by simp) with h9611 | h9611
                  · rcases p9568_3 (m.d 1 3) (by simp) with h9612 | h9612
                    · linarith only [h9272, h9612, hlam]
                    · linarith only [h9271, h9612, hlam]
                  · linarith only [h9269, h9611, hlam]
                · linarith only [h2, h9610, hlam]
              · have p9568_0 := h9568c.1
                have p9568_1 := h9568c.2.1
                have p9568_2 := h9568c.2.2.1
                have p9568_3 := h9568c.2.2.2
                linarith only [hlam, p9568_0]
      · linarith only [h0, h4, h8, h9271, h9272, h9561, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h9620 | h9620
  · linarith only [h2, h9, h9620, hlam]
  · linarith only [h9271, h9619, h9620, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  linarith only [h2, h9, h9623, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  linarith only [h9268, h9271, h9625, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  linarith only [h7, h9, h9268, h9269, h9271, h9619, h9623, h9627, hc24, hc45, hlam, hphi]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  linarith only [h5, h9, h9629, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  linarith only [h7, h9, h9631, hlam]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1_x1_x1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h9269 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h9270 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h9271 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h9619 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h9623 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h9625 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h9627 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h9629 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
    (h9631 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
    (h9633c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 1 2), (m.d 1 3), (m.d 1 4), (m.d 1 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have p9633_0 := h9633c.1
  have p9633_1 := h9633c.2.1
  have p9633_2 := h9633c.2.2.1
  have p9633_3 := h9633c.2.2.2
  linarith only [hlam, p9633_0]

end R2N4
