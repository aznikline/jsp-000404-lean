import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0_x0_x1_x1_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h355 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h416 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h417 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h419 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h421 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
  · rcases h2bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h425 | h425
      · rcases p423_3 (m.d 1 2) (by simp) with h426 | h426
        · linarith only [h0, h426, hlam]
        · rcases p423_3 (m.d 2 3) (by simp) with h428 | h428
          · linarith only [h3, h428, hlam]
          · rcases p423_3 (m.d 2 4) (by simp) with h430 | h430
            · linarith only [h4, h430, hlam]
            · rcases p423_3 (m.d 2 5) (by simp) with h432 | h432
              · linarith only [h432, h5, hlam]
              · rcases h3bigk with h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c | h434c
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h436 | h436
                  · rcases p434_3 (m.d 1 3) (by simp) with h437 | h437
                    · linarith only [h1, h437, hlam]
                    · rcases p434_3 (m.d 2 3) (by simp) with h439 | h439
                      · linarith only [h3, h439, hlam]
                      · rcases p434_3 (m.d 3 4) (by simp) with h441 | h441
                        · linarith only [h441, h6, hlam]
                        · linarith only [h11, h441, hlam]
                  · linarith only [h1, h436, hlam]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h445 | h445
                  · rcases p434_3 (m.d 1 3) (by simp) with h446 | h446
                    · linarith only [h1, h446, hlam]
                    · linarith only [h446, h9, hlam]
                  · linarith only [h3, h445, hlam]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h450 | h450
                  · rcases p434_3 (m.d 1 3) (by simp) with h451 | h451
                    · linarith only [h1, h451, hlam]
                    · rcases p434_3 (m.d 2 3) (by simp) with h453 | h453
                      · linarith only [h3, h453, hlam]
                      · rcases p434_3 (m.d 3 4) (by simp) with h455 | h455
                        · linarith only [h455, hlam, p434_0]
                        · rcases p434_3 (m.d 3 5) (by simp) with h457 | h457
                          · linarith only [h457, h7, hlam]
                          · rcases h5bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              rcases p459_3 (m.d 0 5) (by simp) with h461 | h461
                              · rcases p459_3 (m.d 1 5) (by simp) with h462 | h462
                                · linarith only [h2, h462, hlam]
                                · rcases p459_3 (m.d 2 5) (by simp) with h464 | h464
                                  · linarith only [h464, h5, hlam]
                                  · rcases p459_3 (m.d 3 5) (by simp) with h466 | h466
                                    · linarith only [h466, h7, hlam]
                                    · linarith only [h355, h466, hlam]
                              · linarith only [h2, h461, hlam]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              rcases p459_3 (m.d 0 5) (by simp) with h470 | h470
                              · rcases p459_3 (m.d 1 5) (by simp) with h471 | h471
                                · linarith only [h2, h471, hlam]
                                · linarith only [h10, h471, hlam]
                              · linarith only [h470, h5, hlam]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h0, h3, h355, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              rcases p459_3 (m.d 0 5) (by simp) with h476 | h476
                              · rcases p459_3 (m.d 1 5) (by simp) with h477 | h477
                                · linarith only [h2, h477, hlam]
                                · linarith only [h416, h477, hlam]
                              · linarith only [h476, h8, hlam]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h2, hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h355, hlam, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h0, h11, h3, h416, hc01, hc45, hlam, hphi, ht0b, ht5b, p434_1, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h5, hlam, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h10, hlam, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h419, hlam, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h7, hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h0, h3, h422, hc01, hc45, hlam, hphi, ht0b, ht5b, p434_1, p459_1]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h8, hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h416, hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h421, hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [h422, hlam, p459_0]
                            · have p459_0 := h459c.1
                              have p459_1 := h459c.2.1
                              have p459_2 := h459c.2.2.1
                              have p459_3 := h459c.2.2.2
                              linarith only [hlam, p459_0]
                  · linarith only [h450, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h502 | h502
                  · rcases p434_3 (m.d 1 3) (by simp) with h503 | h503
                    · linarith only [h1, h503, hlam]
                    · rcases p434_3 (m.d 2 3) (by simp) with h505 | h505
                      · linarith only [h3, h505, hlam]
                      · rcases p434_3 (m.d 3 4) (by simp) with h507 | h507
                        · linarith only [h507, h6, hlam]
                        · linarith only [h422, h507, hlam]
                  · linarith only [h502, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h1, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h0, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, p434_1]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h11, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h355, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h3, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h9, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h417, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h419, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h6, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h522 | h522
                  · rcases p434_3 (m.d 1 3) (by simp) with h523 | h523
                    · linarith only [h523, hlam, p434_0]
                    · rcases p434_3 (m.d 2 3) (by simp) with h525 | h525
                      · linarith only [h417, h525, hlam]
                      · rcases p434_3 (m.d 3 4) (by simp) with h527 | h527
                        · rcases p434_3 (m.d 3 5) (by simp) with h528 | h528
                          · linarith only [h422, h528, hlam]
                          · linarith only [h355, h528, hlam]
                        · linarith only [h527, hlam, p434_0]
                  · linarith only [h1, h522, hlam]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h533 | h533
                  · rcases p434_3 (m.d 1 3) (by simp) with h534 | h534
                    · linarith only [h11, h534, hlam]
                    · linarith only [h534, h9, hlam]
                  · linarith only [h3, h533, hlam]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h355, h9, hc23, hc34, hlam, hphi, p434_1]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h7, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h541 | h541
                  · rcases p434_3 (m.d 1 3) (by simp) with h542 | h542
                    · linarith only [h542, hlam, p434_0]
                    · rcases p434_3 (m.d 2 3) (by simp) with h544 | h544
                      · linarith only [h419, h544, hlam]
                      · rcases p434_3 (m.d 3 4) (by simp) with h546 | h546
                        · rcases p434_3 (m.d 3 5) (by simp) with h547 | h547
                          · rcases h5bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              rcases p548_3 (m.d 0 5) (by simp) with h550 | h550
                              · rcases p548_3 (m.d 1 5) (by simp) with h551 | h551
                                · linarith only [h2, h551, hlam]
                                · rcases p548_3 (m.d 2 5) (by simp) with h553 | h553
                                  · linarith only [h5, h553, hlam]
                                  · rcases p548_3 (m.d 3 5) (by simp) with h555 | h555
                                    · linarith only [h555, h7, hlam]
                                    · linarith only [h355, h555, hlam]
                              · linarith only [h2, h550, hlam]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              rcases p548_3 (m.d 0 5) (by simp) with h559 | h559
                              · rcases p548_3 (m.d 1 5) (by simp) with h560 | h560
                                · linarith only [h2, h560, hlam]
                                · linarith only [h10, h560, hlam]
                              · linarith only [h5, h559, hlam]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p434_1, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              rcases p548_3 (m.d 0 5) (by simp) with h565 | h565
                              · rcases p548_3 (m.d 1 5) (by simp) with h566 | h566
                                · linarith only [h2, h566, hlam]
                                · linarith only [h416, h566, hlam]
                              · linarith only [h565, h8, hlam]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h2, hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h2, h419, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h355, hlam, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h0, h10, hc01, hc45, hlam, hphi, ht0b, ht5b, p423_1, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h5, hlam, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h10, hlam, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h419, hlam, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h7, hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h0, h3, h422, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p548_1]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h8, hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h416, hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h421, hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [h422, hlam, p548_0]
                            · have p548_0 := h548c.1
                              have p548_1 := h548c.2.1
                              have p548_2 := h548c.2.2.1
                              have p548_3 := h548c.2.2.2
                              linarith only [hlam, p548_0]
                          · linarith only [h547, hlam, p434_0]
                        · linarith only [h11, h546, hlam]
                  · linarith only [h1, h541, hlam]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  rcases p434_3 (m.d 0 3) (by simp) with h593 | h593
                  · rcases p434_3 (m.d 1 3) (by simp) with h594 | h594
                    · linarith only [h355, h594, hlam]
                    · linarith only [h594, h9, hlam]
                  · linarith only [h3, h593, hlam]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [h422, hlam, p434_0]
                · have p434_0 := h434c.1
                  have p434_1 := h434c.2.1
                  have p434_2 := h434c.2.2.1
                  have p434_3 := h434c.2.2.2
                  linarith only [hlam, p434_0]
      · linarith only [h0, h425, hlam]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h601 | h601
      · rcases p423_3 (m.d 1 2) (by simp) with h602 | h602
        · linarith only [h0, h602, hlam]
        · linarith only [h602, h9, hlam]
      · linarith only [h601, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h606 | h606
      · rcases p423_3 (m.d 1 2) (by simp) with h607 | h607
        · linarith only [h0, h607, hlam]
        · rcases p423_3 (m.d 2 3) (by simp) with h609 | h609
          · linarith only [h3, h609, hlam]
          · rcases p423_3 (m.d 2 4) (by simp) with h611 | h611
            · linarith only [h611, hlam, p423_0]
            · rcases p423_3 (m.d 2 5) (by simp) with h613 | h613
              · linarith only [h5, h613, hlam]
              · rcases h3bigk with h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h617 | h617
                  · rcases p615_3 (m.d 1 3) (by simp) with h618 | h618
                    · linarith only [h1, h618, hlam]
                    · rcases p615_3 (m.d 2 3) (by simp) with h620 | h620
                      · linarith only [h3, h620, hlam]
                      · rcases p615_3 (m.d 3 4) (by simp) with h622 | h622
                        · linarith only [h6, h622, hlam]
                        · linarith only [h11, h622, hlam]
                  · linarith only [h1, h617, hlam]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h626 | h626
                  · rcases p615_3 (m.d 1 3) (by simp) with h627 | h627
                    · linarith only [h1, h627, hlam]
                    · linarith only [h627, h9, hlam]
                  · linarith only [h3, h626, hlam]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h631 | h631
                  · rcases p615_3 (m.d 1 3) (by simp) with h632 | h632
                    · linarith only [h1, h632, hlam]
                    · rcases p615_3 (m.d 2 3) (by simp) with h634 | h634
                      · linarith only [h3, h634, hlam]
                      · rcases p615_3 (m.d 3 4) (by simp) with h636 | h636
                        · linarith only [h636, hlam, p615_0]
                        · rcases p615_3 (m.d 3 5) (by simp) with h638 | h638
                          · linarith only [h638, h7, hlam]
                          · rcases h5bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              rcases p640_3 (m.d 0 5) (by simp) with h642 | h642
                              · rcases p640_3 (m.d 1 5) (by simp) with h643 | h643
                                · linarith only [h2, h643, hlam]
                                · rcases p640_3 (m.d 2 5) (by simp) with h645 | h645
                                  · linarith only [h5, h645, hlam]
                                  · rcases p640_3 (m.d 3 5) (by simp) with h647 | h647
                                    · linarith only [h647, h7, hlam]
                                    · linarith only [h355, h647, hlam]
                              · linarith only [h2, h642, hlam]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              rcases p640_3 (m.d 0 5) (by simp) with h651 | h651
                              · rcases p640_3 (m.d 1 5) (by simp) with h652 | h652
                                · linarith only [h2, h652, hlam]
                                · linarith only [h10, h652, hlam]
                              · linarith only [h5, h651, hlam]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h0, h3, h355, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              rcases p640_3 (m.d 0 5) (by simp) with h657 | h657
                              · rcases p640_3 (m.d 1 5) (by simp) with h658 | h658
                                · linarith only [h2, h658, hlam]
                                · linarith only [h416, h658, hlam]
                              · linarith only [h657, h8, hlam]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h2, hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h355, hlam, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h0, h10, h3, h417, h607, hc01, hc45, hlam, hphi, ht0b, ht5b, p615_1, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h5, hlam, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h10, hlam, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h419, hlam, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h7, hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h0, h3, h422, hc01, hc45, hlam, hphi, ht0b, ht5b, p615_1, p640_1]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h8, hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h416, hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h421, hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [h422, hlam, p640_0]
                            · have p640_0 := h640c.1
                              have p640_1 := h640c.2.1
                              have p640_2 := h640c.2.2.1
                              have p640_3 := h640c.2.2.2
                              linarith only [hlam, p640_0]
                  · linarith only [h631, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h683 | h683
                  · rcases p615_3 (m.d 1 3) (by simp) with h684 | h684
                    · linarith only [h1, h684, hlam]
                    · rcases p615_3 (m.d 2 3) (by simp) with h686 | h686
                      · linarith only [h3, h686, hlam]
                      · rcases p615_3 (m.d 3 4) (by simp) with h688 | h688
                        · linarith only [h6, h688, hlam]
                        · linarith only [h422, h688, hlam]
                  · linarith only [h683, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h1, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h0, h607, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h11, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h355, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h3, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h9, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h417, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h419, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h6, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h703 | h703
                  · rcases p615_3 (m.d 1 3) (by simp) with h704 | h704
                    · linarith only [h704, hlam, p615_0]
                    · rcases p615_3 (m.d 2 3) (by simp) with h706 | h706
                      · linarith only [h417, h706, hlam]
                      · rcases p615_3 (m.d 3 4) (by simp) with h708 | h708
                        · rcases p615_3 (m.d 3 5) (by simp) with h709 | h709
                          · linarith only [h422, h709, hlam]
                          · linarith only [h355, h709, hlam]
                        · linarith only [h708, hlam, p615_0]
                  · linarith only [h1, h703, hlam]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h714 | h714
                  · rcases p615_3 (m.d 1 3) (by simp) with h715 | h715
                    · linarith only [h11, h715, hlam]
                    · linarith only [h715, h9, hlam]
                  · linarith only [h3, h714, hlam]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h355, h9, hc23, hc34, hlam, hphi, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h7, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h722 | h722
                  · rcases p615_3 (m.d 1 3) (by simp) with h723 | h723
                    · linarith only [h723, hlam, p615_0]
                    · rcases p615_3 (m.d 2 3) (by simp) with h725 | h725
                      · linarith only [h419, h725, hlam]
                      · rcases p615_3 (m.d 3 4) (by simp) with h727 | h727
                        · rcases p615_3 (m.d 3 5) (by simp) with h728 | h728
                          · rcases h5bigk with h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c | h729c
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              rcases p729_3 (m.d 0 5) (by simp) with h731 | h731
                              · rcases p729_3 (m.d 1 5) (by simp) with h732 | h732
                                · linarith only [h2, h732, hlam]
                                · rcases p729_3 (m.d 2 5) (by simp) with h734 | h734
                                  · linarith only [h5, h734, hlam]
                                  · rcases p729_3 (m.d 3 5) (by simp) with h736 | h736
                                    · linarith only [h7, h736, hlam]
                                    · linarith only [h355, h736, hlam]
                              · linarith only [h2, h731, hlam]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              rcases p729_3 (m.d 0 5) (by simp) with h740 | h740
                              · rcases p729_3 (m.d 1 5) (by simp) with h741 | h741
                                · linarith only [h2, h741, hlam]
                                · linarith only [h10, h741, hlam]
                              · linarith only [h5, h740, hlam]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p615_1, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              rcases p729_3 (m.d 0 5) (by simp) with h746 | h746
                              · rcases p729_3 (m.d 1 5) (by simp) with h747 | h747
                                · linarith only [h2, h747, hlam]
                                · linarith only [h416, h747, hlam]
                              · linarith only [h746, h8, hlam]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h2, hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h2, h419, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h355, hlam, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h0, h10, h607, hc01, hc45, hlam, hphi, ht0b, ht5b, p423_1, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h5, hlam, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h10, hlam, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h419, hlam, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h7, hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h0, h3, h422, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p729_1]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h8, hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h416, hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h421, hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [h422, hlam, p729_0]
                            · have p729_0 := h729c.1
                              have p729_1 := h729c.2.1
                              have p729_2 := h729c.2.2.1
                              have p729_3 := h729c.2.2.2
                              linarith only [hlam, p729_0]
                          · linarith only [h728, hlam, p615_0]
                        · linarith only [h11, h727, hlam]
                  · linarith only [h1, h722, hlam]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  rcases p615_3 (m.d 0 3) (by simp) with h774 | h774
                  · rcases p615_3 (m.d 1 3) (by simp) with h775 | h775
                    · linarith only [h355, h775, hlam]
                    · linarith only [h775, h9, hlam]
                  · linarith only [h3, h774, hlam]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h422, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
      · linarith only [h606, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h782 | h782
      · rcases p423_3 (m.d 1 2) (by simp) with h783 | h783
        · linarith only [h0, h783, hlam]
        · linarith only [h10, h783, hlam]
      · linarith only [h782, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h0, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h789 | h789
      · rcases p423_3 (m.d 1 2) (by simp) with h790 | h790
        · rcases p423_3 (m.d 2 3) (by simp) with h791 | h791
          · linarith only [h791, hlam, p423_0]
          · rcases p423_3 (m.d 2 4) (by simp) with h793 | h793
            · rcases p423_3 (m.d 2 5) (by simp) with h794 | h794
              · linarith only [h10, h794, hlam]
              · linarith only [h419, h794, hlam]
            · linarith only [h417, h793, hlam]
        · linarith only [h790, hlam, p423_0]
      · linarith only [h3, h789, hlam]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h0, h421, hc01, hc45, hlam, hphi, ht0b, ht5b, p423_1]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h801 | h801
      · rcases p423_3 (m.d 1 2) (by simp) with h802 | h802
        · rcases p423_3 (m.d 2 3) (by simp) with h803 | h803
          · linarith only [h803, h9, hlam]
          · rcases p423_3 (m.d 2 4) (by simp) with h805 | h805
            · rcases p423_3 (m.d 2 5) (by simp) with h806 | h806
              · linarith only [h806, hlam, p423_0]
              · rcases h3bigk with h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c | h808c
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  rcases p808_3 (m.d 0 3) (by simp) with h810 | h810
                  · rcases p808_3 (m.d 1 3) (by simp) with h811 | h811
                    · linarith only [h1, h811, hlam]
                    · rcases p808_3 (m.d 2 3) (by simp) with h813 | h813
                      · linarith only [h3, h813, hlam]
                      · rcases p808_3 (m.d 3 4) (by simp) with h815 | h815
                        · linarith only [h6, h815, hlam]
                        · linarith only [h11, h815, hlam]
                  · linarith only [h1, h810, hlam]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h417, h419, h6, h805, hlam, p423_1, p808_2]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h0, h3, h417, h805, hc01, hc25, hlam, hphi, ht0b, ht5b, p423_1, p808_1]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  rcases p808_3 (m.d 0 3) (by simp) with h821 | h821
                  · rcases p808_3 (m.d 1 3) (by simp) with h822 | h822
                    · linarith only [h1, h822, hlam]
                    · rcases p808_3 (m.d 2 3) (by simp) with h824 | h824
                      · linarith only [h3, h824, hlam]
                      · rcases p808_3 (m.d 3 4) (by simp) with h826 | h826
                        · linarith only [h6, h826, hlam]
                        · linarith only [h422, h826, hlam]
                  · linarith only [h821, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h1, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h355, hc23, hc35, hlam, hphi, p808_1]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h11, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h355, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h3, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h9, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h417, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h419, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h6, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  rcases p808_3 (m.d 0 3) (by simp) with h841 | h841
                  · rcases p808_3 (m.d 1 3) (by simp) with h842 | h842
                    · linarith only [h842, hlam, p808_0]
                    · rcases p808_3 (m.d 2 3) (by simp) with h844 | h844
                      · linarith only [h417, h844, hlam]
                      · rcases p808_3 (m.d 3 4) (by simp) with h846 | h846
                        · rcases p808_3 (m.d 3 5) (by simp) with h847 | h847
                          · linarith only [h422, h847, hlam]
                          · linarith only [h355, h847, hlam]
                        · linarith only [h846, hlam, p808_0]
                  · linarith only [h1, h841, hlam]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  rcases p808_3 (m.d 0 3) (by simp) with h852 | h852
                  · rcases p808_3 (m.d 1 3) (by simp) with h853 | h853
                    · linarith only [h11, h853, hlam]
                    · linarith only [h853, h9, hlam]
                  · linarith only [h3, h852, hlam]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h0, h3, h355, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p808_1]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h7, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  rcases p808_3 (m.d 0 3) (by simp) with h860 | h860
                  · rcases p808_3 (m.d 1 3) (by simp) with h861 | h861
                    · linarith only [h861, hlam, p808_0]
                    · rcases p808_3 (m.d 2 3) (by simp) with h863 | h863
                      · linarith only [h419, h863, hlam]
                      · rcases p808_3 (m.d 3 4) (by simp) with h865 | h865
                        · rcases p808_3 (m.d 3 5) (by simp) with h866 | h866
                          · rcases h5bigk with h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c | h867c
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              rcases p867_3 (m.d 0 5) (by simp) with h869 | h869
                              · rcases p867_3 (m.d 1 5) (by simp) with h870 | h870
                                · linarith only [h2, h870, hlam]
                                · rcases p867_3 (m.d 2 5) (by simp) with h872 | h872
                                  · linarith only [h5, h872, hlam]
                                  · rcases p867_3 (m.d 3 5) (by simp) with h874 | h874
                                    · linarith only [h7, h874, hlam]
                                    · linarith only [h355, h874, hlam]
                              · linarith only [h2, h869, hlam]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              rcases p867_3 (m.d 0 5) (by simp) with h878 | h878
                              · rcases p867_3 (m.d 1 5) (by simp) with h879 | h879
                                · linarith only [h2, h879, hlam]
                                · linarith only [h10, h879, hlam]
                              · linarith only [h5, h878, hlam]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p808_1, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              rcases p867_3 (m.d 0 5) (by simp) with h884 | h884
                              · rcases p867_3 (m.d 1 5) (by simp) with h885 | h885
                                · linarith only [h2, h885, hlam]
                                · linarith only [h416, h885, hlam]
                              · linarith only [h8, h884, hlam]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h2, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h2, h419, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h355, hlam, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h10, hc01, hc45, hlam, hphi, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h5, hlam, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h10, hlam, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h419, hlam, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h7, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h0, h3, h422, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p867_1]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h8, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h416, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h421, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [h422, hlam, p867_0]
                            · have p867_0 := h867c.1
                              have p867_1 := h867c.2.1
                              have p867_2 := h867c.2.2.1
                              have p867_3 := h867c.2.2.2
                              linarith only [hlam, p867_0]
                          · linarith only [h866, hlam, p808_0]
                        · linarith only [h11, h865, hlam]
                  · linarith only [h1, h860, hlam]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  rcases p808_3 (m.d 0 3) (by simp) with h912 | h912
                  · rcases p808_3 (m.d 1 3) (by simp) with h913 | h913
                    · linarith only [h355, h913, hlam]
                    · linarith only [h9, h913, hlam]
                  · linarith only [h3, h912, hlam]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [h422, hlam, p808_0]
                · have p808_0 := h808c.1
                  have p808_1 := h808c.2.1
                  have p808_2 := h808c.2.2.1
                  have p808_3 := h808c.2.2.2
                  linarith only [hlam, p808_0]
            · linarith only [h421, h805, hlam]
        · linarith only [h802, hlam, p423_0]
      · linarith only [h5, h801, hlam]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h3, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h9, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h417, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h419, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h4, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h0, h3, h417, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h929 | h929
      · rcases p423_3 (m.d 1 2) (by simp) with h930 | h930
        · rcases p423_3 (m.d 2 3) (by simp) with h931 | h931
          · linarith only [h417, h931, hlam]
          · rcases p423_3 (m.d 2 4) (by simp) with h933 | h933
            · rcases p423_3 (m.d 2 5) (by simp) with h934 | h934
              · linarith only [h421, h934, hlam]
              · linarith only [h419, h934, hlam]
            · linarith only [h417, h933, hlam]
        · linarith only [h9, h930, hlam]
      · linarith only [h3, h929, hlam]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      rcases p423_3 (m.d 0 2) (by simp) with h941 | h941
      · rcases p423_3 (m.d 1 2) (by simp) with h942 | h942
        · rcases p423_3 (m.d 2 3) (by simp) with h943 | h943
          · linarith only [h417, h943, hlam]
          · rcases p423_3 (m.d 2 4) (by simp) with h945 | h945
            · rcases p423_3 (m.d 2 5) (by simp) with h946 | h946
              · linarith only [h421, h946, hlam]
              · rcases h3bigk with h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c | h948c
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  rcases p948_3 (m.d 0 3) (by simp) with h950 | h950
                  · rcases p948_3 (m.d 1 3) (by simp) with h951 | h951
                    · linarith only [h1, h951, hlam]
                    · rcases p948_3 (m.d 2 3) (by simp) with h953 | h953
                      · linarith only [h3, h953, hlam]
                      · rcases p948_3 (m.d 3 4) (by simp) with h955 | h955
                        · linarith only [h6, h955, hlam]
                        · linarith only [h11, h955, hlam]
                  · linarith only [h1, h950, hlam]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h417, h419, h6, hlam, p423_1, p948_2]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h0, h3, h417, hc01, hc25, hlam, hphi, ht0b, ht5b, p423_1, p948_1]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  rcases p948_3 (m.d 0 3) (by simp) with h961 | h961
                  · rcases p948_3 (m.d 1 3) (by simp) with h962 | h962
                    · linarith only [h1, h962, hlam]
                    · rcases p948_3 (m.d 2 3) (by simp) with h964 | h964
                      · linarith only [h3, h964, hlam]
                      · rcases p948_3 (m.d 3 4) (by simp) with h966 | h966
                        · linarith only [h6, h966, hlam]
                        · linarith only [h422, h966, hlam]
                  · linarith only [h961, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h1, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h355, hc23, hc35, hlam, hphi, p948_1]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h11, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h355, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h3, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h9, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h417, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h419, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h6, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  rcases p948_3 (m.d 0 3) (by simp) with h981 | h981
                  · rcases p948_3 (m.d 1 3) (by simp) with h982 | h982
                    · linarith only [h982, hlam, p948_0]
                    · rcases p948_3 (m.d 2 3) (by simp) with h984 | h984
                      · linarith only [h417, h984, hlam]
                      · rcases p948_3 (m.d 3 4) (by simp) with h986 | h986
                        · rcases p948_3 (m.d 3 5) (by simp) with h987 | h987
                          · linarith only [h422, h987, hlam]
                          · linarith only [h355, h987, hlam]
                        · linarith only [h986, hlam, p948_0]
                  · linarith only [h1, h981, hlam]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  rcases p948_3 (m.d 0 3) (by simp) with h992 | h992
                  · rcases p948_3 (m.d 1 3) (by simp) with h993 | h993
                    · linarith only [h11, h993, hlam]
                    · linarith only [h9, h993, hlam]
                  · linarith only [h3, h992, hlam]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h0, h3, h355, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p948_1]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h7, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  rcases p948_3 (m.d 0 3) (by simp) with h1000 | h1000
                  · rcases p948_3 (m.d 1 3) (by simp) with h1001 | h1001
                    · linarith only [h1001, hlam, p948_0]
                    · rcases p948_3 (m.d 2 3) (by simp) with h1003 | h1003
                      · linarith only [h1003, h419, hlam]
                      · rcases p948_3 (m.d 3 4) (by simp) with h1005 | h1005
                        · rcases p948_3 (m.d 3 5) (by simp) with h1006 | h1006
                          · rcases h5bigk with h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              rcases p1007_3 (m.d 0 5) (by simp) with h1009 | h1009
                              · rcases p1007_3 (m.d 1 5) (by simp) with h1010 | h1010
                                · linarith only [h1010, h2, hlam]
                                · rcases p1007_3 (m.d 2 5) (by simp) with h1012 | h1012
                                  · linarith only [h1012, h5, hlam]
                                  · rcases p1007_3 (m.d 3 5) (by simp) with h1014 | h1014
                                    · linarith only [h1014, h7, hlam]
                                    · linarith only [h1014, h355, hlam]
                              · linarith only [h1009, h2, hlam]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              rcases p1007_3 (m.d 0 5) (by simp) with h1018 | h1018
                              · rcases p1007_3 (m.d 1 5) (by simp) with h1019 | h1019
                                · linarith only [h1019, h2, hlam]
                                · linarith only [h10, h1019, hlam]
                              · linarith only [h1018, h5, hlam]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h0, h3, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1007_1, p948_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              rcases p1007_3 (m.d 0 5) (by simp) with h1024 | h1024
                              · rcases p1007_3 (m.d 1 5) (by simp) with h1025 | h1025
                                · linarith only [h1025, h2, hlam]
                                · linarith only [h1025, h416, hlam]
                              · linarith only [h1024, h8, hlam]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h2, hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h2, h419, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h355, hlam, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h0, h11, h3, h416, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h5, hlam, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h10, hlam, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h419, hlam, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1007_1, p423_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h7, hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h0, h3, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h0, h3, h422, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p1007_1]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h8, hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h416, hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h421, hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [h422, hlam, p1007_0]
                            · have p1007_0 := h1007c.1
                              have p1007_1 := h1007c.2.1
                              have p1007_2 := h1007c.2.2.1
                              have p1007_3 := h1007c.2.2.2
                              linarith only [hlam, p1007_0]
                          · linarith only [h1006, hlam, p948_0]
                        · linarith only [h1005, h11, hlam]
                  · linarith only [h1, h1000, hlam]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  rcases p948_3 (m.d 0 3) (by simp) with h1052 | h1052
                  · rcases p948_3 (m.d 1 3) (by simp) with h1053 | h1053
                    · linarith only [h1053, h355, hlam]
                    · linarith only [h1053, h9, hlam]
                  · linarith only [h1052, h3, hlam]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [h422, hlam, p948_0]
                · have p948_0 := h948c.1
                  have p948_1 := h948c.2.1
                  have p948_2 := h948c.2.2.1
                  have p948_3 := h948c.2.2.2
                  linarith only [hlam, p948_0]
            · linarith only [h421, h945, hlam]
        · linarith only [h10, h942, hlam]
      · linarith only [h5, h941, hlam]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h5, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h10, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h0, h10, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p423_1]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [h421, hlam, p423_0]
    · have p423_0 := h423c.1
      have p423_1 := h423c.2.1
      have p423_2 := h423c.2.2.1
      have p423_3 := h423c.2.2.2
      linarith only [hlam, p423_0]
  · linarith only [h11, h416, h422, hlam]

end R2N4
