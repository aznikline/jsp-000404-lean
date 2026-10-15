import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S39

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12790000 in
set_option maxHeartbeats 12790000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s19 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  have h20408 := hg20408
  rcases m.htr 0 2 4 (by decide) (by decide) with h20409 | h20409
  · exact r1l7_10_12_23_L_I_L_I_H_I_s20 m hb0 hb2 hb3 h0 h14396 h16915 h18815 h20408 h20409
  · rcases m.htr 0 2 5 (by decide) (by decide) with h26400 | h26400
    · rcases m.htr 0 3 4 (by decide) (by decide) with h26401 | h26401
      · linarith only [h20408, h20409, h26401, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h26403 | h26403
        · rcases m.htr 0 4 5 (by decide) (by decide) with h26404 | h26404
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26405 | h26405
            · rcases m.htr 1 2 4 (by decide) (by decide) with h26406 | h26406
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26407 | h26407
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26408 | h26408
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26409 | h26409
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26410 | h26410
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26411 | h26411
                        · linarith only [h20408, h20409, h26401, h26406, h26411, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26413 | h26413
                          · linarith only [h20408, h20409, h26405, h26408, h26411, h26413, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h20408, h20409, h26403, h26405, h26408, h26411, h26413, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h16915, h26404, h26410, hlam]
                    · linarith only [h26401, h26403, h26409, hc13, hc34, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26418 | h26418
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26419 | h26419
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26420 | h26420
                        · linarith only [h20408, h20409, h26406, h26420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26422 | h26422
                          · linarith only [h20408, h20409, h26406, h26422, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h20408, h20409, h26403, h26406, h26422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h20408, h20409, h26403, h26404, h26406, h26419, hlam]
                    · linarith only [h20408, h20409, h26403, h26406, h26418, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h20409, h26400, h26406, h26407, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26428 | h26428
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26429 | h26429
                  · linarith only [h26401, h26403, h26405, h26406, h26429, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26431 | h26431
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26432 | h26432
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26433 | h26433
                        · linarith only [h0, h20408, h26406, h26429, h26433, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26435 | h26435
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26436 | h26436
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26437 | h26437
                              · rcases h0bigk with h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c | h26438c
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [hlam, p26438_0]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h0, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h14396, hlam, p26438_0]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h16915, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h18815, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h0, h26406, h26433, hc01, hc34, hlam, hphi, ht12, ht23, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [hlam, p26438_0]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h0, h20408, h26406, h26433, h26435, h26437, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h20409, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h0, h18815, h26406, h26433, hc01, hc34, hlam, hphi, ht12, ht23, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h0, h20408, h26406, h26433, hc01, hc34, hlam, hphi, ht12, ht23, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h20408, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [hlam, p26438_0]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h26401, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h0, h18815, h20408, h26406, h26433, hc01, hc34, hlam, hphi, ht12, ht23, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  rcases p26438_3 (m.d 0 1) (by simp) with h26454 | h26454
                                  · linarith only [h16915, h26454, hlam]
                                  · rcases p26438_3 (m.d 0 2) (by simp) with h26456 | h26456
                                    · linarith only [h20409, h26456, hlam]
                                    · linarith only [h0, h26456, hlam]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h16915, h20408, h26435, h26437, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  rcases p26438_3 (m.d 0 1) (by simp) with h26460 | h26460
                                  · linarith only [h16915, h26460, hlam]
                                  · rcases p26438_3 (m.d 0 2) (by simp) with h26462 | h26462
                                    · linarith only [h20409, h26462, hlam]
                                    · linarith only [h20408, h26462, hlam]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [hlam, p26438_0]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  rcases p26438_3 (m.d 0 1) (by simp) with h26466 | h26466
                                  · linarith only [h16915, h26466, hlam]
                                  · rcases p26438_3 (m.d 0 2) (by simp) with h26468 | h26468
                                    · linarith only [h20409, h26468, hlam]
                                    · linarith only [h26400, h26468, hlam]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h0, h26400, h26406, h26433, hc01, hc34, hlam, hphi, ht12, ht23, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h26400, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h26403, hlam, p26438_0]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [h26404, hlam, p26438_1]
                                · have p26438_0 := h26438c.1
                                  have p26438_1 := h26438c.2.1
                                  have p26438_2 := h26438c.2.2.1
                                  have p26438_3 := h26438c.2.2.2
                                  linarith only [hlam, p26438_0]
                              · linarith only [h0, h26406, h26433, h26437, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h20408, h26403, h26404, h26406, h26436, hlam]
                          · linarith only [h0, h20408, h26403, h26406, h26433, h26435, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h16915, h20408, h26403, h26404, h26406, h26432, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h14396, h20408, h26403, h26406, h26431, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h26400, h26428, hlam]
            · linarith only [h0, h20408, h26405, hlam]
          · linarith only [h20408, h20409, h26403, h26404, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h26484 | h26484
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26485 | h26485
            · rcases m.htr 1 2 4 (by decide) (by decide) with h26486 | h26486
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26487 | h26487
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26488 | h26488
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26489 | h26489
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26490 | h26490
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26491 | h26491
                        · linarith only [h20408, h20409, h26401, h26486, h26491, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26493 | h26493
                          · linarith only [h14396, h20408, h20409, h26403, h26485, h26488, h26491, h26493, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26495 | h26495
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26496 | h26496
                              · rcases h0bigk with h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c | h26497c
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [hlam, p26497_0]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h0, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h14396, hlam, p26497_0]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h16915, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h18815, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h20409, h26485, h26488, h26491, hc01, hc12, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [hlam, p26497_0]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h14396, h20409, h26485, h26488, h26491, hc01, hc12, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h20409, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h20409, h26485, h26488, h26491, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h26403, h26489, hc01, hc15, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h20408, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [hlam, p26497_0]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h26401, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h26403, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h20409, h26485, h26488, h26491, hc01, hc12, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h20409, h26400, h26485, h26488, h26491, h26493, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h14396, h20409, h26485, h26488, h26491, hc01, hc12, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [hlam, p26497_0]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h14396, h20409, h26403, h26485, h26488, h26491, hc01, hc12, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h20409, h26400, h26485, h26488, h26491, hc01, hc12, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h26400, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h14396, h20409, h26400, h26485, h26488, h26491, hc01, hc12, hlam, hphi, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [h26484, hlam, p26497_1]
                                · have p26497_0 := h26497c.1
                                  have p26497_1 := h26497c.2.1
                                  have p26497_2 := h26497c.2.2.1
                                  have p26497_3 := h26497c.2.2.2
                                  linarith only [hlam, p26497_0]
                              · linarith only [h20408, h20409, h26491, h26496, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h20409, h26400, h26484, h26495, hlam]
                      · linarith only [h16915, h20409, h26400, h26484, h26490, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h20408, h20409, h26401, h26488, h26489, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26527 | h26527
                    · linarith only [h14396, h26403, h26488, h26527, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26529 | h26529
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26530 | h26530
                        · linarith only [h20408, h20409, h26488, h26530, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26532 | h26532
                          · linarith only [h14396, h20408, h20409, h26486, h26527, h26532, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26534 | h26534
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26535 | h26535
                              · rcases h0bigk with h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c | h26536c
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [hlam, p26536_0]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h0, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h14396, hlam, p26536_0]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h16915, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h18815, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h20409, h26486, hc01, hc12, hlam, hphi, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [hlam, p26536_0]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h14396, h20409, h26486, hc01, hc12, hlam, hphi, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h20409, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h20409, h26486, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h14396, h26527, hc01, hc35, hlam, hphi, ht12, ht23, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h20408, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [hlam, p26536_0]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h26401, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h26403, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h20409, h26486, hc01, hc12, hlam, hphi, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h20409, h26400, h26486, h26532, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h14396, h20409, h26486, hc01, hc12, hlam, hphi, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [hlam, p26536_0]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h14396, h20409, h26403, h26486, hc01, hc12, hlam, hphi, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h20409, h26400, h26486, hc01, hc12, hlam, hphi, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h26400, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h14396, h20409, h26400, h26486, hc01, hc12, hlam, hphi, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [h26484, hlam, p26536_1]
                                · have p26536_0 := h26536c.1
                                  have p26536_1 := h26536c.2.1
                                  have p26536_2 := h26536c.2.2.1
                                  have p26536_3 := h26536c.2.2.2
                                  linarith only [hlam, p26536_0]
                              · linarith only [h14396, h26488, h26535, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h20409, h26400, h26484, h26534, hlam]
                      · linarith only [h20409, h26400, h26484, h26486, h26529, hlam]
                · linarith only [h20409, h26400, h26486, h26487, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26566 | h26566
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26567 | h26567
                  · linarith only [h14396, h26401, h26485, h26486, h26567, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26569 | h26569
                    · linarith only [h14396, h26403, h26485, h26486, h26569, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26571 | h26571
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26572 | h26572
                        · linarith only [h0, h16915, h20408, h26486, h26567, h26572, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26574 | h26574
                          · linarith only [h14396, h26569, h26574, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26576 | h26576
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26577 | h26577
                              · rcases h0bigk with h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c | h26578c
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [hlam, p26578_0]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h0, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h14396, hlam, p26578_0]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h16915, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h18815, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h0, h26486, h26572, hc01, hc34, hlam, hphi, ht12, ht23, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [hlam, p26578_0]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h0, h26486, h26572, hc03, hc34, hlam, hphi, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h20409, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h0, h18815, h26486, h26572, hc01, hc34, hlam, hphi, ht12, ht23, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h14396, h26569, hc01, hc35, hlam, hphi, ht12, ht23, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h20408, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [hlam, p26578_0]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h26401, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h26403, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  rcases p26578_3 (m.d 0 1) (by simp) with h26594 | h26594
                                  · linarith only [h16915, h26594, hlam]
                                  · rcases p26578_3 (m.d 0 2) (by simp) with h26596 | h26596
                                    · linarith only [h20409, h26596, hlam]
                                    · linarith only [h0, h26596, hlam]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h20409, h26400, h26572, h26574, hc23, hc34, hlam, hphi, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  rcases p26578_3 (m.d 0 1) (by simp) with h26600 | h26600
                                  · linarith only [h16915, h26600, hlam]
                                  · rcases p26578_3 (m.d 0 2) (by simp) with h26602 | h26602
                                    · linarith only [h20409, h26602, hlam]
                                    · linarith only [h20408, h26602, hlam]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [hlam, p26578_0]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  rcases p26578_3 (m.d 0 1) (by simp) with h26606 | h26606
                                  · linarith only [h16915, h26606, hlam]
                                  · rcases p26578_3 (m.d 0 2) (by simp) with h26608 | h26608
                                    · linarith only [h20409, h26608, hlam]
                                    · linarith only [h26400, h26608, hlam]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h20409, h26400, h26572, hc01, hc34, hlam, hphi, ht12, ht23, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h26400, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h20409, h26400, h26572, hc03, hc34, hlam, hphi, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [h26484, hlam, p26578_1]
                                · have p26578_0 := h26578c.1
                                  have p26578_1 := h26578c.2.1
                                  have p26578_2 := h26578c.2.2.1
                                  have p26578_3 := h26578c.2.2.2
                                  linarith only [hlam, p26578_0]
                              · linarith only [h0, h26486, h26572, h26577, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h14396, h26484, h26486, h26566, h26569, h26576, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h16915, h20409, h26400, h26484, h26571, hlam]
                · linarith only [h14396, h16915, h20409, h26400, h26485, h26566, hc01, hc14, hlam, hphi]
            · linarith only [h0, h20408, h26485, hlam]
          · linarith only [h20409, h26400, h26484, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h26622 | h26622
      · linarith only [h20408, h20409, h26622, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h26624 | h26624
        · linarith only [h20408, h26400, h26624, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h26626 | h26626
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26627 | h26627
            · rcases m.htr 1 2 4 (by decide) (by decide) with h26628 | h26628
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26629 | h26629
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26630 | h26630
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26631 | h26631
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26632 | h26632
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26633 | h26633
                        · linarith only [h20408, h20409, h26622, h26628, h26633, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26635 | h26635
                          · linarith only [h14396, h20408, h20409, h26624, h26627, h26630, h26633, h26635, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26637 | h26637
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26638 | h26638
                              · rcases h0bigk with h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c | h26639c
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [hlam, p26639_0]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h0, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h14396, hlam, p26639_0]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h16915, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h18815, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h26400, h26627, h26630, h26633, h26637, hc01, hc12, hlam, hphi, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [hlam, p26639_0]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h14396, h26400, h26627, h26630, h26633, h26637, hc01, hc12, hlam, hphi, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h20409, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h26400, hlam, p26639_0]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h20408, h26400, h26627, h26630, h26633, h26637, hc01, hc12, hlam, hphi, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h20408, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [hlam, p26639_0]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h26622, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h26624, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h20409, h26627, h26630, h26633, hc01, hc12, hlam, hphi, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h20408, h20409, h26627, h26630, h26633, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h14396, h20409, h26627, h26630, h26633, hc01, hc12, hlam, hphi, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [hlam, p26639_0]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h20408, h20409, h26400, h26627, h26630, h26633, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h26400, h26627, h26630, h26633, h26637, hc01, hc12, hlam, hphi, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h20408, h26400, h26627, h26630, h26633, h26637, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h14396, h26400, h26627, h26630, h26633, h26637, hc01, hc12, hlam, hphi, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [h26626, hlam, p26639_1]
                                · have p26639_0 := h26639c.1
                                  have p26639_1 := h26639c.2.1
                                  have p26639_2 := h26639c.2.2.1
                                  have p26639_3 := h26639c.2.2.2
                                  linarith only [hlam, p26639_0]
                              · linarith only [h20409, h26626, h26633, h26638, hlam]
                            · linarith only [h20409, h26626, h26637, hlam]
                      · linarith only [h16915, h20409, h26626, h26632, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h20408, h20409, h26622, h26630, h26631, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26669 | h26669
                    · linarith only [h14396, h26624, h26630, h26669, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26671 | h26671
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26672 | h26672
                        · linarith only [h20408, h20409, h26628, h26630, h26672, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26674 | h26674
                          · linarith only [h20408, h26400, h26629, h26669, h26674, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26676 | h26676
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26677 | h26677
                              · rcases h0bigk with h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c | h26678c
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [hlam, p26678_0]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h0, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h14396, hlam, p26678_0]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h16915, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h18815, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h26400, h26628, h26676, hc01, hc12, hlam, hphi, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [hlam, p26678_0]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h14396, h26400, h26628, h26676, hc01, hc12, hlam, hphi, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h20409, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h26400, hlam, p26678_0]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h20408, h26400, h26628, h26676, hc01, hc12, hlam, hphi, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h20408, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [hlam, p26678_0]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h26622, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h26624, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h20409, h26628, hc01, hc12, hlam, hphi, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h20408, h20409, h26628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h14396, h20409, h26628, hc01, hc12, hlam, hphi, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [hlam, p26678_0]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h20408, h20409, h26400, h26628, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h26400, h26628, h26676, hc01, hc12, hlam, hphi, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h20408, h26400, h26628, h26676, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h14396, h26400, h26628, h26676, hc01, hc12, hlam, hphi, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [h26626, hlam, p26678_1]
                                · have p26678_0 := h26678c.1
                                  have p26678_1 := h26678c.2.1
                                  have p26678_2 := h26678c.2.2.1
                                  have p26678_3 := h26678c.2.2.2
                                  linarith only [hlam, p26678_0]
                              · linarith only [h20409, h26626, h26628, h26630, h26677, hlam]
                            · linarith only [h20409, h26626, h26676, hlam]
                      · linarith only [h20409, h26626, h26628, h26671, hlam]
                · linarith only [h20408, h20409, h26628, h26629, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26708 | h26708
                · linarith only [h20408, h26400, h26628, h26708, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26710 | h26710
                  · linarith only [h14396, h26622, h26627, h26628, h26710, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26712 | h26712
                    · linarith only [h14396, h26624, h26710, h26712, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26714 | h26714
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26715 | h26715
                        · linarith only [h0, h20408, h26628, h26710, h26715, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26717 | h26717
                          · linarith only [h14396, h20408, h26712, h26717, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26719 | h26719
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h26720 | h26720
                              · rcases h0bigk with h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c | h26721c
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [hlam, p26721_0]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h0, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h14396, hlam, p26721_0]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h16915, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h18815, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h0, h26708, h26715, h26719, hc01, hc34, hlam, hphi, ht12, ht23, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [hlam, p26721_0]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h0, h26708, h26715, h26719, hc03, hc34, hlam, hphi, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h20409, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h26400, hlam, p26721_0]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h0, h20408, h26708, h26715, h26719, hc01, hc34, hlam, hphi, ht12, ht23, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h20408, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [hlam, p26721_0]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h26622, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h26624, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  rcases p26721_3 (m.d 0 1) (by simp) with h26737 | h26737
                                  · linarith only [h16915, h26737, hlam]
                                  · rcases p26721_3 (m.d 0 2) (by simp) with h26739 | h26739
                                    · linarith only [h20409, h26739, hlam]
                                    · linarith only [h0, h26739, hlam]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h16915, h20408, h26628, h26715, hc23, hc34, hlam, hphi, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  rcases p26721_3 (m.d 0 1) (by simp) with h26743 | h26743
                                  · linarith only [h16915, h26743, hlam]
                                  · rcases p26721_3 (m.d 0 2) (by simp) with h26745 | h26745
                                    · linarith only [h20409, h26745, hlam]
                                    · linarith only [h20408, h26745, hlam]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [hlam, p26721_0]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h16915, h20408, h26400, h26628, h26715, hc23, hc34, hlam, hphi, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  rcases p26721_3 (m.d 0 1) (by simp) with h26750 | h26750
                                  · linarith only [h18815, h26750, hlam]
                                  · rcases p26721_3 (m.d 0 2) (by simp) with h26752 | h26752
                                    · linarith only [h26400, h26752, hlam]
                                    · linarith only [h0, h26752, hlam]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h18815, h20408, h26628, h26714, h26715, hc23, hc34, hlam, hphi, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  rcases p26721_3 (m.d 0 1) (by simp) with h26756 | h26756
                                  · linarith only [h18815, h26756, hlam]
                                  · rcases p26721_3 (m.d 0 2) (by simp) with h26758 | h26758
                                    · linarith only [h26400, h26758, hlam]
                                    · linarith only [h20408, h26758, hlam]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [h26626, hlam, p26721_1]
                                · have p26721_0 := h26721c.1
                                  have p26721_1 := h26721c.2.1
                                  have p26721_2 := h26721c.2.2.1
                                  have p26721_3 := h26721c.2.2.2
                                  linarith only [hlam, p26721_0]
                              · linarith only [h0, h26708, h26715, h26719, h26720, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h14396, h26626, h26627, h26628, h26719, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h16915, h26626, h26714, hlam]
            · linarith only [h0, h20408, h26627, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h26767 | h26767
            · rcases m.htr 1 2 4 (by decide) (by decide) with h26768 | h26768
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26769 | h26769
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26770 | h26770
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26771 | h26771
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26772 | h26772
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26773 | h26773
                        · linarith only [h14396, h20408, h20409, h26622, h26626, h26767, h26770, h26772, h26773, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26775 | h26775
                          · linarith only [h20408, h20409, h26626, h26767, h26770, h26772, h26775, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26777 | h26777
                            · linarith only [h20408, h20409, h26626, h26767, h26770, h26773, h26777, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h20408, h20409, h26777, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h20408, h20409, h26768, h26772, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h14396, h26622, h26770, h26771, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26782 | h26782
                    · linarith only [h14396, h26624, h26770, h26782, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26784 | h26784
                      · linarith only [h20408, h20409, h26626, h26770, h26784, hc23, hc34, hlam, hphi]
                      · linarith only [h20408, h20409, h26768, h26784, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h20408, h20409, h26768, h26769, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h26788 | h26788
                · linarith only [h20408, h26400, h26768, h26788, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h26790 | h26790
                  · linarith only [h14396, h26622, h26767, h26768, h26790, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26792 | h26792
                    · linarith only [h14396, h26624, h26790, h26792, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26794 | h26794
                      · linarith only [h20408, h20409, h26626, h26790, h26794, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h26796 | h26796
                        · linarith only [h0, h20408, h26768, h26794, h26796, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h26798 | h26798
                          · linarith only [h20408, h26624, h26798, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h26800 | h26800
                            · linarith only [h0, h26768, h26794, h26796, h26800, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h20408, h20409, h26800, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h20408, h20409, h26767, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  exact r1l7_10_12_23_L_I_L_I_H_I_s19 m hb0 hb2 hb3 h0 h14396 h16915 h18815 h20408

end R2N4
