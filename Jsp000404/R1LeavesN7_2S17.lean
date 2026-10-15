import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9116000 in
set_option maxHeartbeats 9116000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s11_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h8360 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  rcases m.htr 0 3 5 (by decide) (by decide) with h8362 | h8362
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8363 | h8363
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8364 | h8364
      · linarith only [h0, h4, h8360, h8364, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h8366 | h8366
        · linarith only [h0, h7337, h8366, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h8368 | h8368
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8369 | h8369
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8370 | h8370
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8371 | h8371
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8372 | h8372
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8373 | h8373
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8374 | h8374
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8375 | h8375
                        · rcases h0bigk with h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c | h8376c
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8378 | h8378
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8379 | h8379
                              · linarith only [h0, h8379, hlam]
                              · rcases p8376_3 (m.d 0 3) (by simp) with h8381 | h8381
                                · linarith only [h1, h8381, hlam]
                                · linarith only [h4, h8381, hlam]
                            · linarith only [h0, h8378, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h8361, h8375, hc01, hc45, hlam, hphi, ht0b, ht5b, p8376_1]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8386 | h8386
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8387 | h8387
                              · linarith only [h0, h8387, hlam]
                              · rcases p8376_3 (m.d 0 3) (by simp) with h8389 | h8389
                                · linarith only [h1, h8389, hlam]
                                · linarith only [h8361, h8389, hlam]
                            · linarith only [h2, h8386, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8393 | h8393
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8394 | h8394
                              · linarith only [h0, h8394, hlam]
                              · linarith only [h8360, h8394, hlam]
                            · linarith only [h3, h8393, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h0, hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h4, hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h7337, hlam, p8376_1]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8402 | h8402
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8403 | h8403
                              · rcases p8376_3 (m.d 0 3) (by simp) with h8404 | h8404
                                · rcases p8376_3 (m.d 0 4) (by simp) with h8405 | h8405
                                  · rcases p8376_3 (m.d 0 5) (by simp) with h8406 | h8406
                                    · linarith only [h8360, h8406, hlam]
                                    · rcases h2bigk with h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c | h8408c
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h7337, h8372, hc12, hc23, hlam, hphi, p8408_1]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h4, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h7337, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        rcases p8408_3 (m.d 0 2) (by simp) with h8413 | h8413
                                        · rcases p8408_3 (m.d 1 2) (by simp) with h8414 | h8414
                                          · linarith only [h0, h8414, hlam]
                                          · linarith only [h8368, h8414, hlam]
                                        · linarith only [h8413, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h0, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h8364, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h8366, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        rcases p8408_3 (m.d 0 2) (by simp) with h8422 | h8422
                                        · rcases p8408_3 (m.d 1 2) (by simp) with h8423 | h8423
                                          · rcases p8408_3 (m.d 2 3) (by simp) with h8424 | h8424
                                            · rcases p8408_3 (m.d 2 4) (by simp) with h8425 | h8425
                                              · rcases p8408_3 (m.d 2 5) (by simp) with h8426 | h8426
                                                · linarith only [h8426, hlam, p8408_0]
                                                · rcases h3bigk with h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c | h8428c
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h4, h8364, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8408_1, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h4, hlam, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h4, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    rcases p8428_3 (m.d 0 3) (by simp) with h8433 | h8433
                                                    · rcases p8428_3 (m.d 1 3) (by simp) with h8434 | h8434
                                                      · linarith only [h1, h8434, hlam]
                                                      · linarith only [h8370, h8434, hlam]
                                                    · linarith only [h8433, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h1, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8364, hlam, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8375, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h1, h8375, hc01, hc45, hlam, hphi, ht0b, ht5b, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h4, hc02, hc23, hlam, hphi, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8364, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8408_1, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    rcases p8428_3 (m.d 0 3) (by simp) with h8447 | h8447
                                                    · linarith only [h4, h8447, hlam]
                                                    · linarith only [h8362, h8447, hlam]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8361, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8369, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8372, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8361, h8375, hc03, hc45, hlam, hphi, ht0b, ht5b, p8428_1]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8362, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8370, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8373, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [h8375, hlam, p8428_0]
                                                  · have p8428_0 := h8428c.1
                                                    have p8428_1 := h8428c.2.1
                                                    have p8428_2 := h8428c.2.2.1
                                                    have p8428_3 := h8428c.2.2.2
                                                    linarith only [hlam, p8428_0]
                                              · linarith only [h8374, h8425, hlam]
                                            · linarith only [h8373, h8424, hlam]
                                          · linarith only [h8423, hlam, p8408_0]
                                        · linarith only [h8360, h8422, hlam]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h3, h8368, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8408_1]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        rcases p8408_3 (m.d 0 2) (by simp) with h8465 | h8465
                                        · linarith only [h4, h8465, hlam]
                                        · linarith only [h0, h8465, hlam]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h3, h7337, h8368, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8408_1]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h3, h4, h8368, hlam, p8376_1, p8408_2]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h3, h8368, h8373, h8375, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8408_1]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        rcases p8408_3 (m.d 0 2) (by simp) with h8472 | h8472
                                        · linarith only [h7337, h8472, hlam]
                                        · linarith only [h0, h8472, hlam]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h8372, hlam, p8408_1]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h3, h7337, h8368, hlam, p8376_1, p8408_2]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h8360, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h8368, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h8373, hlam, p8408_1]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [h8374, hlam, p8408_0]
                                      · have p8408_0 := h8408c.1
                                        have p8408_1 := h8408c.2.1
                                        have p8408_2 := h8408c.2.2.1
                                        have p8408_3 := h8408c.2.2.2
                                        linarith only [hlam, p8408_0]
                                  · linarith only [h8363, h8405, hlam]
                                · linarith only [h8362, h8404, hlam]
                              · linarith only [h8360, h8403, hlam]
                            · linarith only [h3, h8402, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h1, hlam, p8376_1]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8488 | h8488
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8489 | h8489
                              · linarith only [h4, h8489, hlam]
                              · rcases p8376_3 (m.d 0 3) (by simp) with h8491 | h8491
                                · rcases p8376_3 (m.d 0 4) (by simp) with h8492 | h8492
                                  · linarith only [h8361, h8492, hlam]
                                  · linarith only [h7337, h8492, hlam]
                                · linarith only [h4, h8491, hlam]
                            · linarith only [h0, h8488, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8498 | h8498
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8499 | h8499
                              · linarith only [h4, h8499, hlam]
                              · rcases p8376_3 (m.d 0 3) (by simp) with h8501 | h8501
                                · rcases p8376_3 (m.d 0 4) (by simp) with h8502 | h8502
                                  · linarith only [h8361, h8502, hlam]
                                  · rcases p8376_3 (m.d 0 5) (by simp) with h8504 | h8504
                                    · linarith only [h8362, h8504, hlam]
                                    · rcases h2bigk with h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c | h8506c
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h4, h7337, h8368, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8506_1]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h4, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h7337, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h4, h7337, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8506_1]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h0, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h8364, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h8366, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h0, h4, h7337, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8506_1]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        rcases p8506_3 (m.d 0 2) (by simp) with h8517 | h8517
                                        · linarith only [h8517, hlam, p8506_0]
                                        · rcases p8506_3 (m.d 1 2) (by simp) with h8519 | h8519
                                          · linarith only [h8364, h8519, hlam]
                                          · rcases p8506_3 (m.d 2 3) (by simp) with h8521 | h8521
                                            · rcases p8506_3 (m.d 2 4) (by simp) with h8522 | h8522
                                              · linarith only [h8372, h8522, hlam]
                                              · linarith only [h7337, h8522, hlam]
                                            · linarith only [h8521, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        rcases p8506_3 (m.d 0 2) (by simp) with h8526 | h8526
                                        · linarith only [h4, h8526, hlam]
                                        · linarith only [h0, h8526, hlam]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h7337, hc02, hc23, hlam, hphi, p8506_1]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h0, h4, h7337, h8368, hlam, p8376_1, p8506_2]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        rcases p8506_3 (m.d 0 2) (by simp) with h8532 | h8532
                                        · linarith only [h8532, hlam, p8506_0]
                                        · rcases p8506_3 (m.d 1 2) (by simp) with h8534 | h8534
                                          · linarith only [h8366, h8534, hlam]
                                          · rcases p8506_3 (m.d 2 3) (by simp) with h8536 | h8536
                                            · rcases p8506_3 (m.d 2 4) (by simp) with h8537 | h8537
                                              · rcases p8506_3 (m.d 2 5) (by simp) with h8538 | h8538
                                                · linarith only [h8374, h8538, hlam]
                                                · rcases h3bigk with h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c | h8540c
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8364, h8368, h8373, h8375, hc03, hc45, hlam, hphi, ht0b, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h4, hlam, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h4, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    rcases p8540_3 (m.d 0 3) (by simp) with h8545 | h8545
                                                    · rcases p8540_3 (m.d 1 3) (by simp) with h8546 | h8546
                                                      · linarith only [h1, h8546, hlam]
                                                      · linarith only [h8370, h8546, hlam]
                                                    · linarith only [h8545, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h1, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8364, hlam, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8375, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h1, h8375, hc01, hc45, hlam, hphi, ht0b, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h0, h4, h8368, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8364, h8368, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    rcases p8540_3 (m.d 0 3) (by simp) with h8559 | h8559
                                                    · linarith only [h4, h8559, hlam]
                                                    · linarith only [h8362, h8559, hlam]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8361, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8369, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8372, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8369, h8375, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8540_1]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8362, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8370, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8373, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [h8375, hlam, p8540_0]
                                                  · have p8540_0 := h8540c.1
                                                    have p8540_1 := h8540c.2.1
                                                    have p8540_2 := h8540c.2.2.1
                                                    have p8540_3 := h8540c.2.2.2
                                                    linarith only [hlam, p8540_0]
                                              · linarith only [h8537, hlam, p8506_0]
                                            · linarith only [h4, h8536, hlam]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        rcases p8506_3 (m.d 0 2) (by simp) with h8574 | h8574
                                        · linarith only [h7337, h8574, hlam]
                                        · linarith only [h0, h8574, hlam]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h8372, hlam, p8506_1]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        rcases p8506_3 (m.d 0 2) (by simp) with h8579 | h8579
                                        · linarith only [h7337, h8579, hlam]
                                        · linarith only [h8360, h8579, hlam]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h8360, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h8368, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h8373, hlam, p8506_1]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [h8374, hlam, p8506_0]
                                      · have p8506_0 := h8506c.1
                                        have p8506_1 := h8506c.2.1
                                        have p8506_2 := h8506c.2.2.1
                                        have p8506_3 := h8506c.2.2.2
                                        linarith only [hlam, p8506_0]
                                · linarith only [h8361, h8501, hlam]
                            · linarith only [h2, h8498, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8589 | h8589
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8590 | h8590
                              · linarith only [h4, h8590, hlam]
                              · linarith only [h8360, h8590, hlam]
                            · linarith only [h3, h8589, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h2, hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8595 | h8595
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8596 | h8596
                              · linarith only [h7337, h8596, hlam]
                              · rcases p8376_3 (m.d 0 3) (by simp) with h8598 | h8598
                                · rcases p8376_3 (m.d 0 4) (by simp) with h8599 | h8599
                                  · rcases p8376_3 (m.d 0 5) (by simp) with h8600 | h8600
                                    · linarith only [h8363, h8600, hlam]
                                    · rcases h2bigk with h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c | h8602c
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8368, h8373, h8375, hc04, hc45, hlam, hphi, ht0b, ht5b, p8376_1, p8602_1]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h4, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h7337, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h7337, h8373, h8375, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8602_1]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h0, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8364, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8366, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h0, h7337, h8373, h8375, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8376_1, p8602_1]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        rcases p8602_3 (m.d 0 2) (by simp) with h8613 | h8613
                                        · linarith only [h8613, hlam, p8602_0]
                                        · rcases p8602_3 (m.d 1 2) (by simp) with h8615 | h8615
                                          · linarith only [h8364, h8615, hlam]
                                          · rcases p8602_3 (m.d 2 3) (by simp) with h8617 | h8617
                                            · rcases p8602_3 (m.d 2 4) (by simp) with h8618 | h8618
                                              · linarith only [h8372, h8618, hlam]
                                              · linarith only [h7337, h8618, hlam]
                                            · linarith only [h8617, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        rcases p8602_3 (m.d 0 2) (by simp) with h8622 | h8622
                                        · linarith only [h4, h8622, hlam]
                                        · linarith only [h0, h8622, hlam]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h7337, hc02, hc23, hlam, hphi, p8602_1]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h0, h4, h8361, h8368, hlam, p8376_1, p8602_2]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        rcases p8602_3 (m.d 0 2) (by simp) with h8628 | h8628
                                        · linarith only [h8628, hlam, p8602_0]
                                        · rcases p8602_3 (m.d 1 2) (by simp) with h8630 | h8630
                                          · linarith only [h8366, h8630, hlam]
                                          · rcases p8602_3 (m.d 2 3) (by simp) with h8632 | h8632
                                            · rcases p8602_3 (m.d 2 4) (by simp) with h8633 | h8633
                                              · rcases p8602_3 (m.d 2 5) (by simp) with h8634 | h8634
                                                · linarith only [h8374, h8634, hlam]
                                                · rcases h3bigk with h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c | h8636c
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8364, h8368, h8373, h8375, hc03, hc45, hlam, hphi, ht0b, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h4, hlam, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h4, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    rcases p8636_3 (m.d 0 3) (by simp) with h8641 | h8641
                                                    · rcases p8636_3 (m.d 1 3) (by simp) with h8642 | h8642
                                                      · linarith only [h1, h8642, hlam]
                                                      · linarith only [h8370, h8642, hlam]
                                                    · linarith only [h8641, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h1, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8364, hlam, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8375, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h1, h8375, hc01, hc45, hlam, hphi, ht0b, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h0, h4, h8368, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8364, h8368, h8373, h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8375, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    rcases p8636_3 (m.d 0 3) (by simp) with h8655 | h8655
                                                    · linarith only [h4, h8655, hlam]
                                                    · linarith only [h8362, h8655, hlam]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8361, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8369, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8372, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8369, h8375, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8636_1]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8362, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8370, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8373, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [h8375, hlam, p8636_0]
                                                  · have p8636_0 := h8636c.1
                                                    have p8636_1 := h8636c.2.1
                                                    have p8636_2 := h8636c.2.2.1
                                                    have p8636_3 := h8636c.2.2.2
                                                    linarith only [hlam, p8636_0]
                                              · linarith only [h8633, hlam, p8602_0]
                                            · linarith only [h4, h8632, hlam]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        rcases p8602_3 (m.d 0 2) (by simp) with h8670 | h8670
                                        · linarith only [h7337, h8670, hlam]
                                        · linarith only [h0, h8670, hlam]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8372, hlam, p8602_1]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h0, h7337, h8368, hlam, p8376_1, p8602_2]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8360, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8368, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8373, hlam, p8602_1]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [h8374, hlam, p8602_0]
                                      · have p8602_0 := h8602c.1
                                        have p8602_1 := h8602c.2.1
                                        have p8602_2 := h8602c.2.2.1
                                        have p8602_3 := h8602c.2.2.2
                                        linarith only [hlam, p8602_0]
                                  · linarith only [h7337, h8599, hlam]
                                · linarith only [h4, h8598, hlam]
                            · linarith only [h0, h8595, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h8361, hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            rcases p8376_3 (m.d 0 1) (by simp) with h8686 | h8686
                            · rcases p8376_3 (m.d 0 2) (by simp) with h8687 | h8687
                              · linarith only [h7337, h8687, hlam]
                              · linarith only [h8360, h8687, hlam]
                            · linarith only [h3, h8686, hlam]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h3, hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h8360, hlam, p8376_1]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h8362, hlam, p8376_0]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [h8363, hlam, p8376_1]
                          · have p8376_0 := h8376c.1
                            have p8376_1 := h8376c.2.1
                            have p8376_2 := h8376c.2.2.1
                            have p8376_3 := h8376c.2.2.2
                            linarith only [hlam, p8376_0]
                        · rcases h0bigk with h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c | h8696c
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h0, h8368, h8374, h8375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h2, h8361, h8366, h8368, h8374, h8375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h2, h8366, h8368, h8374, h8375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            rcases p8696_3 (m.d 0 1) (by simp) with h8701 | h8701
                            · rcases p8696_3 (m.d 0 2) (by simp) with h8702 | h8702
                              · linarith only [h0, h8702, hlam]
                              · linarith only [h8360, h8702, hlam]
                            · linarith only [h3, h8701, hlam]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h0, hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h4, hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h7337, hlam, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h3, h4, h8368, h8374, h8375, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h1, hlam, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h0, h8368, h8374, h8375, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h2, h4, h8366, h8368, h8374, h8375, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            rcases p8696_3 (m.d 0 1) (by simp) with h8715 | h8715
                            · rcases p8696_3 (m.d 0 2) (by simp) with h8716 | h8716
                              · linarith only [h4, h8716, hlam]
                              · linarith only [h8360, h8716, hlam]
                            · linarith only [h3, h8715, hlam]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h2, hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h0, h8368, h8374, h8375, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h8361, hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            rcases p8696_3 (m.d 0 1) (by simp) with h8724 | h8724
                            · rcases p8696_3 (m.d 0 2) (by simp) with h8725 | h8725
                              · linarith only [h7337, h8725, hlam]
                              · linarith only [h8360, h8725, hlam]
                            · linarith only [h3, h8724, hlam]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h3, hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h8360, hlam, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h8362, hlam, p8696_0]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [h8363, hlam, p8696_1]
                          · have p8696_0 := h8696c.1
                            have p8696_1 := h8696c.2.1
                            have p8696_2 := h8696c.2.2.1
                            have p8696_3 := h8696c.2.2.2
                            linarith only [hlam, p8696_0]
                      · linarith only [h0, h7337, h8363, h8368, h8374, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h8362, h8373, hlam]
                  · linarith only [h0, h4, h8361, h8368, h8372, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h8366, h8368, h8371, hlam]
              · linarith only [h8366, h8368, h8369, h8370, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h8739 | h8739
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8740 | h8740
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8741 | h8741
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h8742 | h8742
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h8743 | h8743
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h8744 | h8744
                        · rcases h0bigk with h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            rcases p8745_3 (m.d 0 1) (by simp) with h8747 | h8747
                            · rcases p8745_3 (m.d 0 2) (by simp) with h8748 | h8748
                              · linarith only [h0, h8748, hlam]
                              · rcases p8745_3 (m.d 0 3) (by simp) with h8750 | h8750
                                · linarith only [h1, h8750, hlam]
                                · linarith only [h4, h8750, hlam]
                            · linarith only [h0, h8747, hlam]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h8361, h8364, h8369, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8745_1]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h8361, h8364, h8368, h8369, h8742, h8744, hc01, hc45, hlam, hphi, ht0b, ht5b, p8745_1]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            rcases p8745_3 (m.d 0 1) (by simp) with h8756 | h8756
                            · rcases p8745_3 (m.d 0 2) (by simp) with h8757 | h8757
                              · linarith only [h0, h8757, hlam]
                              · linarith only [h8360, h8757, hlam]
                            · linarith only [h3, h8756, hlam]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h0, hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h4, hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h7337, hlam, p8745_1]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            rcases p8745_3 (m.d 0 1) (by simp) with h8765 | h8765
                            · rcases p8745_3 (m.d 0 2) (by simp) with h8766 | h8766
                              · rcases p8745_3 (m.d 0 3) (by simp) with h8767 | h8767
                                · rcases p8745_3 (m.d 0 4) (by simp) with h8768 | h8768
                                  · rcases p8745_3 (m.d 0 5) (by simp) with h8769 | h8769
                                    · linarith only [h8360, h8769, hlam]
                                    · rcases h2bigk with h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c | h8771c
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h7337, h8368, h8741, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8771_1]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h4, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h7337, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        rcases p8771_3 (m.d 0 2) (by simp) with h8776 | h8776
                                        · rcases p8771_3 (m.d 1 2) (by simp) with h8777 | h8777
                                          · linarith only [h0, h8777, hlam]
                                          · linarith only [h8368, h8777, hlam]
                                        · linarith only [h8776, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h0, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8364, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8366, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8361, h8364, h8369, h8742, h8744, hc03, hc45, hlam, hphi, ht0b, ht5b, p8771_1]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8745_1, p8771_1]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        rcases p8771_3 (m.d 0 2) (by simp) with h8787 | h8787
                                        · linarith only [h4, h8787, hlam]
                                        · linarith only [h0, h8787, hlam]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h3, h7337, h8368, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8745_1, p8771_1]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h3, h4, h8368, hlam, p8745_1, p8771_2]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p8745_1, p8771_1]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        rcases p8771_3 (m.d 0 2) (by simp) with h8794 | h8794
                                        · linarith only [h7337, h8794, hlam]
                                        · linarith only [h0, h8794, hlam]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8741, hlam, p8771_1]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h3, h7337, h8368, hlam, p8745_1, p8771_2]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8360, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8368, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8742, hlam, p8771_1]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [h8743, hlam, p8771_0]
                                      · have p8771_0 := h8771c.1
                                        have p8771_1 := h8771c.2.1
                                        have p8771_2 := h8771c.2.2.1
                                        have p8771_3 := h8771c.2.2.2
                                        linarith only [hlam, p8771_0]
                                  · linarith only [h8363, h8768, hlam]
                                · linarith only [h8362, h8767, hlam]
                              · linarith only [h8360, h8766, hlam]
                            · linarith only [h3, h8765, hlam]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h1, hlam, p8745_1]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            rcases p8745_3 (m.d 0 1) (by simp) with h8810 | h8810
                            · rcases p8745_3 (m.d 0 2) (by simp) with h8811 | h8811
                              · linarith only [h4, h8811, hlam]
                              · rcases p8745_3 (m.d 0 3) (by simp) with h8813 | h8813
                                · rcases p8745_3 (m.d 0 4) (by simp) with h8814 | h8814
                                  · linarith only [h8361, h8814, hlam]
                                  · linarith only [h7337, h8814, hlam]
                                · linarith only [h4, h8813, hlam]
                            · linarith only [h0, h8810, hlam]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h4, h8361, h8364, h8369, hc12, hc23, hlam, hphi, p8745_1]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            rcases p8745_3 (m.d 0 1) (by simp) with h8821 | h8821
                            · rcases p8745_3 (m.d 0 2) (by simp) with h8822 | h8822
                              · linarith only [h4, h8822, hlam]
                              · linarith only [h8360, h8822, hlam]
                            · linarith only [h3, h8821, hlam]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h2, hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            rcases p8745_3 (m.d 0 1) (by simp) with h8827 | h8827
                            · rcases p8745_3 (m.d 0 2) (by simp) with h8828 | h8828
                              · linarith only [h7337, h8828, hlam]
                              · rcases p8745_3 (m.d 0 3) (by simp) with h8830 | h8830
                                · rcases p8745_3 (m.d 0 4) (by simp) with h8831 | h8831
                                  · rcases p8745_3 (m.d 0 5) (by simp) with h8832 | h8832
                                    · linarith only [h8363, h8832, hlam]
                                    · rcases h2bigk with h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c | h8834c
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h4, h8361, h8368, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8745_1, p8834_1]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h4, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h7337, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h4, h8361, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8745_1, p8834_1]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h0, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h8364, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h8366, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h0, h4, h8361, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8745_1, p8834_1]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        rcases p8834_3 (m.d 0 2) (by simp) with h8845 | h8845
                                        · linarith only [h8845, hlam, p8834_0]
                                        · rcases p8834_3 (m.d 1 2) (by simp) with h8847 | h8847
                                          · linarith only [h8364, h8847, hlam]
                                          · rcases p8834_3 (m.d 2 3) (by simp) with h8849 | h8849
                                            · rcases p8834_3 (m.d 2 4) (by simp) with h8850 | h8850
                                              · linarith only [h8741, h8850, hlam]
                                              · linarith only [h7337, h8850, hlam]
                                            · linarith only [h8849, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        rcases p8834_3 (m.d 0 2) (by simp) with h8854 | h8854
                                        · linarith only [h4, h8854, hlam]
                                        · linarith only [h0, h8854, hlam]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h7337, hc02, hc23, hlam, hphi, p8745_1, p8834_1]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h4, h8361, h8364, h8368, h8369, hlam, p8834_2]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        rcases p8834_3 (m.d 0 2) (by simp) with h8860 | h8860
                                        · linarith only [h8860, hlam, p8834_0]
                                        · rcases p8834_3 (m.d 1 2) (by simp) with h8862 | h8862
                                          · linarith only [h8366, h8862, hlam]
                                          · rcases p8834_3 (m.d 2 3) (by simp) with h8864 | h8864
                                            · rcases p8834_3 (m.d 2 4) (by simp) with h8865 | h8865
                                              · rcases p8834_3 (m.d 2 5) (by simp) with h8866 | h8866
                                                · linarith only [h8743, h8866, hlam]
                                                · rcases h3bigk with h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c | h8868c
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8364, h8368, h8742, h8744, hc03, hc45, hlam, hphi, ht0b, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h4, hlam, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h4, h8364, h8368, h8369, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    rcases p8868_3 (m.d 0 3) (by simp) with h8873 | h8873
                                                    · rcases p8868_3 (m.d 1 3) (by simp) with h8874 | h8874
                                                      · linarith only [h1, h8874, hlam]
                                                      · linarith only [h8739, h8874, hlam]
                                                    · linarith only [h8873, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h1, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8364, hlam, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8369, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8369, h8744, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h0, h4, h8368, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8364, h8368, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8366, h8368, h8369, h8742, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    rcases p8868_3 (m.d 0 3) (by simp) with h8887 | h8887
                                                    · linarith only [h4, h8887, hlam]
                                                    · linarith only [h8362, h8887, hlam]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8361, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8364, h8368, h8742, h8744, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8741, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h4, h8361, h8744, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8868_1]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8362, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8739, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8742, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [h8744, hlam, p8868_0]
                                                  · have p8868_0 := h8868c.1
                                                    have p8868_1 := h8868c.2.1
                                                    have p8868_2 := h8868c.2.2.1
                                                    have p8868_3 := h8868c.2.2.2
                                                    linarith only [hlam, p8868_0]
                                              · linarith only [h8865, hlam, p8834_0]
                                            · linarith only [h4, h8864, hlam]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        rcases p8834_3 (m.d 0 2) (by simp) with h8902 | h8902
                                        · linarith only [h7337, h8902, hlam]
                                        · linarith only [h0, h8902, hlam]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h8741, hlam, p8834_1]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h0, h7337, h8368, hlam, p8745_1, p8834_2]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h8360, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h8368, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h8742, hlam, p8834_1]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [h8743, hlam, p8834_0]
                                      · have p8834_0 := h8834c.1
                                        have p8834_1 := h8834c.2.1
                                        have p8834_2 := h8834c.2.2.1
                                        have p8834_3 := h8834c.2.2.2
                                        linarith only [hlam, p8834_0]
                                  · linarith only [h7337, h8831, hlam]
                                · linarith only [h4, h8830, hlam]
                            · linarith only [h0, h8827, hlam]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h8361, hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            rcases p8745_3 (m.d 0 1) (by simp) with h8918 | h8918
                            · rcases p8745_3 (m.d 0 2) (by simp) with h8919 | h8919
                              · linarith only [h7337, h8919, hlam]
                              · linarith only [h8360, h8919, hlam]
                            · linarith only [h3, h8918, hlam]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h3, hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h8360, hlam, p8745_1]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h8362, hlam, p8745_0]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [h8363, hlam, p8745_1]
                          · have p8745_0 := h8745c.1
                            have p8745_1 := h8745c.2.1
                            have p8745_2 := h8745c.2.2.1
                            have p8745_3 := h8745c.2.2.2
                            linarith only [hlam, p8745_0]
                        · linarith only [h4, h8361, h8363, h8364, h8368, h8369, h8742, h8744, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h7337, h8363, h8743, hlam]
                    · linarith only [h4, h8361, h8364, h8368, h8369, h8742, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h4, h8361, h8741, hlam]
                · linarith only [h8364, h8368, h8369, h8740, hlam]
              · linarith only [h8364, h8368, h8739, hlam]
          · linarith only [h7337, h8360, h8368, hc12, hc24, hlam, hphi]
    · linarith only [h7337, h8360, h8363, hlam]
  · linarith only [h7337, h8360, h8361, h8362, hlam]

end R2N4
