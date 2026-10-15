import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S34

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11350000 in
set_option maxHeartbeats 11350000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x0_x1 (m : N7Model)
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
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13284 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h13285 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h13286 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h13425 | h13425
  · rcases m.htr 1 2 5 (by decide) (by decide) with h13426 | h13426
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13427 | h13427
      · linarith only [h13286, h13427, h4, h7, hlam]
      · linarith only [h13286, h13425, h13427, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13430 | h13430
      · linarith only [h13284, h13425, h13426, h13430, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · linarith only [h13286, h13425, h13430, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h13433 | h13433
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13434 | h13434
      · linarith only [h1, h13284, h13434, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h13436 | h13436
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13437 | h13437
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13438 | h13438
            · linarith only [h13438, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13440 | h13440
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13441 | h13441
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13442 | h13442
                  · rcases h1bigk with h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c | h13443c
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      rcases p13443_3 (m.d 0 1) (by simp) with h13445 | h13445
                      · rcases p13443_3 (m.d 1 2) (by simp) with h13446 | h13446
                        · linarith only [h13446, hlam, p13443_0]
                        · rcases p13443_3 (m.d 1 3) (by simp) with h13448 | h13448
                          · linarith only [h1, h13448, hlam]
                          · linarith only [h13286, h13448, hlam]
                      · linarith only [h13445, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      rcases p13443_3 (m.d 0 1) (by simp) with h13452 | h13452
                      · rcases p13443_3 (m.d 1 2) (by simp) with h13453 | h13453
                        · linarith only [h0, h13453, hlam]
                        · rcases p13443_3 (m.d 1 3) (by simp) with h13455 | h13455
                          · linarith only [h13455, hlam, p13443_0]
                          · rcases p13443_3 (m.d 1 4) (by simp) with h13457 | h13457
                            · linarith only [h13457, h2, hlam]
                            · linarith only [h13434, h13457, hlam]
                      · linarith only [h13452, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      rcases p13443_3 (m.d 0 1) (by simp) with h13461 | h13461
                      · rcases p13443_3 (m.d 1 2) (by simp) with h13462 | h13462
                        · linarith only [h0, h13462, hlam]
                        · rcases p13443_3 (m.d 1 3) (by simp) with h13464 | h13464
                          · linarith only [h1, h13464, hlam]
                          · rcases p13443_3 (m.d 1 4) (by simp) with h13466 | h13466
                            · linarith only [h13466, hlam, p13443_0]
                            · rcases p13443_3 (m.d 1 5) (by simp) with h13468 | h13468
                              · linarith only [h13468, h3, hlam]
                              · rcases h1emax with h13470 | h13470 | h13470 | h13470 | h13470
                                · linarith only [h0, h13433, h13440, h13442, h13470, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases h2bigk with h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c | h13472c
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    rcases p13472_3 (m.d 0 2) (by simp) with h13474 | h13474
                                    · rcases p13472_3 (m.d 1 2) (by simp) with h13475 | h13475
                                      · linarith only [h0, h13475, hlam]
                                      · rcases p13472_3 (m.d 2 3) (by simp) with h13477 | h13477
                                        · linarith only [h13477, h4, hlam]
                                        · linarith only [h13286, h13477, hlam]
                                    · linarith only [h0, h13474, hlam]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h0, h13286, h13433, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h0, h13286, h13433, h13438, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13286, h13433, h4, hlam, p13472_2]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h0, hlam, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13286, hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13425, hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13286, h13440, h13442, h4, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h4, hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13438, hlam, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    rcases p13472_3 (m.d 0 2) (by simp) with h13493 | h13493
                                    · rcases p13472_3 (m.d 1 2) (by simp) with h13494 | h13494
                                      · linarith only [h13286, h13494, hlam]
                                      · linarith only [h13433, h13494, hlam]
                                    · linarith only [h13493, h6, hlam]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h5, hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13433, h13440, h13442, h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13286, h13433, h13440, h13442, h5, hc04, hc45, hlam, hphi, ht0b, ht5b, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    rcases p13472_3 (m.d 0 2) (by simp) with h13502 | h13502
                                    · rcases p13472_3 (m.d 1 2) (by simp) with h13503 | h13503
                                      · linarith only [h13425, h13503, hlam]
                                      · linarith only [h13433, h13503, hlam]
                                    · linarith only [h13502, h6, hlam]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h6, hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13433, hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13440, hlam, p13472_0]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [h13441, hlam, p13472_1]
                                  · have p13472_0 := h13472c.1
                                    have p13472_1 := h13472c.2.1
                                    have p13472_2 := h13472c.2.2.1
                                    have p13472_3 := h13472c.2.2.2
                                    linarith only [hlam, p13472_0]
                                · rcases h2bigk with h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c | h13512c
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    rcases p13512_3 (m.d 0 2) (by simp) with h13514 | h13514
                                    · rcases p13512_3 (m.d 1 2) (by simp) with h13515 | h13515
                                      · linarith only [h0, h13515, hlam]
                                      · rcases p13512_3 (m.d 2 3) (by simp) with h13517 | h13517
                                        · linarith only [h13517, h4, hlam]
                                        · linarith only [h13286, h13517, hlam]
                                    · linarith only [h0, h13514, hlam]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h0, h13286, h13433, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h0, h13425, h13433, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13286, h13433, h4, hlam, p13512_2]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h0, hlam, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13286, hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13425, hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13286, h13434, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13443_1, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h4, hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13438, hlam, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    rcases p13512_3 (m.d 0 2) (by simp) with h13533 | h13533
                                    · rcases p13512_3 (m.d 1 2) (by simp) with h13534 | h13534
                                      · linarith only [h13286, h13534, hlam]
                                      · linarith only [h13433, h13534, hlam]
                                    · linarith only [h13533, h6, hlam]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h5, hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h0, h13433, h13440, h13442, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h0, h13286, h13433, h13440, h13442, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    rcases p13512_3 (m.d 0 2) (by simp) with h13542 | h13542
                                    · rcases p13512_3 (m.d 1 2) (by simp) with h13543 | h13543
                                      · linarith only [h13425, h13543, hlam]
                                      · linarith only [h13433, h13543, hlam]
                                    · linarith only [h13542, h6, hlam]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h6, hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13433, hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13440, hlam, p13512_0]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [h13441, hlam, p13512_1]
                                  · have p13512_0 := h13512c.1
                                    have p13512_1 := h13512c.2.1
                                    have p13512_2 := h13512c.2.2.1
                                    have p13512_3 := h13512c.2.2.2
                                    linarith only [hlam, p13512_0]
                                · rcases h2bigk with h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c | h13552c
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    rcases p13552_3 (m.d 0 2) (by simp) with h13554 | h13554
                                    · rcases p13552_3 (m.d 1 2) (by simp) with h13555 | h13555
                                      · linarith only [h0, h13555, hlam]
                                      · rcases p13552_3 (m.d 2 3) (by simp) with h13557 | h13557
                                        · linarith only [h13557, h4, hlam]
                                        · linarith only [h13286, h13557, hlam]
                                    · linarith only [h0, h13554, hlam]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h0, h13286, h13433, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h0, h13425, h13433, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13286, h13433, h4, hlam, p13552_2]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h0, hlam, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13286, hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13425, hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13286, h13440, h13442, h4, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h4, hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13438, hlam, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    rcases p13552_3 (m.d 0 2) (by simp) with h13573 | h13573
                                    · rcases p13552_3 (m.d 1 2) (by simp) with h13574 | h13574
                                      · linarith only [h13286, h13574, hlam]
                                      · linarith only [h13433, h13574, hlam]
                                    · linarith only [h13573, h6, hlam]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h5, hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13433, h13440, h13442, h5, hc02, hc45, hlam, hphi, ht0b, ht5b, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h0, h13286, h13433, h13440, h13442, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    rcases p13552_3 (m.d 0 2) (by simp) with h13582 | h13582
                                    · rcases p13552_3 (m.d 1 2) (by simp) with h13583 | h13583
                                      · linarith only [h13425, h13583, hlam]
                                      · linarith only [h13433, h13583, hlam]
                                    · linarith only [h13582, h6, hlam]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h6, hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13433, hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13440, hlam, p13552_0]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [h13441, hlam, p13552_1]
                                  · have p13552_0 := h13552c.1
                                    have p13552_1 := h13552c.2.1
                                    have p13552_2 := h13552c.2.2.1
                                    have p13552_3 := h13552c.2.2.2
                                    linarith only [hlam, p13552_0]
                                · rcases h2bigk with h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c | h13592c
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    rcases p13592_3 (m.d 0 2) (by simp) with h13594 | h13594
                                    · rcases p13592_3 (m.d 1 2) (by simp) with h13595 | h13595
                                      · linarith only [h0, h13595, hlam]
                                      · rcases p13592_3 (m.d 2 3) (by simp) with h13597 | h13597
                                        · linarith only [h13597, h4, hlam]
                                        · linarith only [h13286, h13597, hlam]
                                    · linarith only [h0, h13594, hlam]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h0, h13286, h13433, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h0, h13425, h13433, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13286, h13433, h4, hlam, p13592_2]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h0, hlam, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13286, hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13425, hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13286, h13434, h13440, h13442, hc01, hc45, hlam, hphi, ht0b, ht5b, p13443_1, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h4, hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13438, hlam, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    rcases p13592_3 (m.d 0 2) (by simp) with h13613 | h13613
                                    · rcases p13592_3 (m.d 1 2) (by simp) with h13614 | h13614
                                      · linarith only [h13286, h13614, hlam]
                                      · linarith only [h13433, h13614, hlam]
                                    · linarith only [h13613, h6, hlam]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h5, hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h0, h13433, h13440, h13442, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h0, h13286, h13433, h13440, h13442, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    rcases p13592_3 (m.d 0 2) (by simp) with h13622 | h13622
                                    · rcases p13592_3 (m.d 1 2) (by simp) with h13623 | h13623
                                      · linarith only [h13425, h13623, hlam]
                                      · linarith only [h13433, h13623, hlam]
                                    · linarith only [h13622, h6, hlam]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h6, hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13433, hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13440, hlam, p13592_0]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [h13441, hlam, p13592_1]
                                  · have p13592_0 := h13592c.1
                                    have p13592_1 := h13592c.2.1
                                    have p13592_2 := h13592c.2.2.1
                                    have p13592_3 := h13592c.2.2.2
                                    linarith only [hlam, p13592_0]
                      · linarith only [h13461, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      rcases p13443_3 (m.d 0 1) (by simp) with h13633 | h13633
                      · rcases p13443_3 (m.d 1 2) (by simp) with h13634 | h13634
                        · linarith only [h0, h13634, hlam]
                        · linarith only [h13433, h13634, hlam]
                      · linarith only [h13633, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h0, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h13286, hlam, p13443_1]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h13425, hlam, p13443_1]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h0, h13286, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p13443_1]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h1, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h1, h7, hc12, hc34, hlam, hphi, ht23, p13443_1]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h13434, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      rcases p13443_3 (m.d 0 1) (by simp) with h13647 | h13647
                      · rcases p13443_3 (m.d 1 2) (by simp) with h13648 | h13648
                        · linarith only [h13286, h13648, hlam]
                        · linarith only [h13433, h13648, hlam]
                      · linarith only [h13647, h3, hlam]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h2, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h0, h13425, h13433, h13440, h13442, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p13443_1]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h0, h13286, h13425, h13433, h13440, h13442, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p13443_1]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      rcases p13443_3 (m.d 0 1) (by simp) with h13656 | h13656
                      · rcases p13443_3 (m.d 1 2) (by simp) with h13657 | h13657
                        · linarith only [h13425, h13657, hlam]
                        · linarith only [h13433, h13657, hlam]
                      · linarith only [h13656, h3, hlam]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h3, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h13433, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h13436, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [h13437, hlam, p13443_0]
                    · have p13443_0 := h13443c.1
                      have p13443_1 := h13443c.2.1
                      have p13443_2 := h13443c.2.2.1
                      have p13443_3 := h13443c.2.2.2
                      linarith only [hlam, p13443_0]
                  · linarith only [h13286, h13442, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h13425, h13433, h13437, h13440, h13441, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h13284, h13286, h13433, h13440, hc03, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h13286, h13433, h13434, h13437, hlam]
        · linarith only [h13284, h13286, h13436, h7, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13671 | h13671
      · linarith only [h1, h13284, h13671, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h13673 | h13673
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13674 | h13674
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13675 | h13675
            · linarith only [h13675, h4, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13677 | h13677
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13678 | h13678
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13679 | h13679
                  · rcases h1bigk with h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c | h13680c
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      rcases p13680_3 (m.d 0 1) (by simp) with h13682 | h13682
                      · rcases p13680_3 (m.d 1 2) (by simp) with h13683 | h13683
                        · linarith only [h13683, hlam, p13680_0]
                        · rcases p13680_3 (m.d 1 3) (by simp) with h13685 | h13685
                          · linarith only [h1, h13685, hlam]
                          · linarith only [h13286, h13685, hlam]
                      · linarith only [h13682, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      rcases p13680_3 (m.d 0 1) (by simp) with h13689 | h13689
                      · rcases p13680_3 (m.d 1 2) (by simp) with h13690 | h13690
                        · linarith only [h0, h13690, hlam]
                        · rcases p13680_3 (m.d 1 3) (by simp) with h13692 | h13692
                          · linarith only [h13692, hlam, p13680_0]
                          · rcases p13680_3 (m.d 1 4) (by simp) with h13694 | h13694
                            · linarith only [h13694, h2, hlam]
                            · linarith only [h13671, h13694, hlam]
                      · linarith only [h13689, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      rcases p13680_3 (m.d 0 1) (by simp) with h13698 | h13698
                      · rcases p13680_3 (m.d 1 2) (by simp) with h13699 | h13699
                        · linarith only [h0, h13699, hlam]
                        · rcases p13680_3 (m.d 1 3) (by simp) with h13701 | h13701
                          · linarith only [h1, h13701, hlam]
                          · rcases p13680_3 (m.d 1 4) (by simp) with h13703 | h13703
                            · linarith only [h13703, hlam, p13680_0]
                            · rcases p13680_3 (m.d 1 5) (by simp) with h13705 | h13705
                              · linarith only [h13705, h3, hlam]
                              · rcases h1emax with h13707 | h13707 | h13707 | h13707 | h13707
                                · linarith only [h13671, h13707, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13680_1]
                                · rcases h2bigk with h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c | h13709c
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    rcases p13709_3 (m.d 0 2) (by simp) with h13711 | h13711
                                    · rcases p13709_3 (m.d 1 2) (by simp) with h13712 | h13712
                                      · linarith only [h0, h13712, hlam]
                                      · rcases p13709_3 (m.d 2 3) (by simp) with h13714 | h13714
                                        · linarith only [h13714, h4, hlam]
                                        · linarith only [h13286, h13714, hlam]
                                    · linarith only [h0, h13711, hlam]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    rcases p13709_3 (m.d 0 2) (by simp) with h13718 | h13718
                                    · rcases p13709_3 (m.d 1 2) (by simp) with h13719 | h13719
                                      · linarith only [h0, h13719, hlam]
                                      · rcases p13709_3 (m.d 2 3) (by simp) with h13721 | h13721
                                        · linarith only [h13721, hlam, p13709_0]
                                        · rcases p13709_3 (m.d 2 4) (by simp) with h13723 | h13723
                                          · linarith only [h13723, h5, hlam]
                                          · linarith only [h13675, h13723, hlam]
                                    · linarith only [h13718, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    rcases p13709_3 (m.d 0 2) (by simp) with h13727 | h13727
                                    · rcases p13709_3 (m.d 1 2) (by simp) with h13728 | h13728
                                      · linarith only [h0, h13728, hlam]
                                      · rcases p13709_3 (m.d 2 3) (by simp) with h13730 | h13730
                                        · linarith only [h13730, h4, hlam]
                                        · rcases p13709_3 (m.d 2 4) (by simp) with h13732 | h13732
                                          · linarith only [h13732, hlam, p13709_0]
                                          · rcases p13709_3 (m.d 2 5) (by simp) with h13734 | h13734
                                            · linarith only [h13734, h6, hlam]
                                            · rcases h4bigk with h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c | h13736c
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                rcases p13736_3 (m.d 0 4) (by simp) with h13738 | h13738
                                                · rcases p13736_3 (m.d 1 4) (by simp) with h13739 | h13739
                                                  · linarith only [h13739, h2, hlam]
                                                  · rcases p13736_3 (m.d 2 4) (by simp) with h13741 | h13741
                                                    · linarith only [h13741, h5, hlam]
                                                    · linarith only [h13425, h13741, hlam]
                                                · linarith only [h13738, h2, hlam]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13433, h13675, h13677, h7, hc12, hc34, hlam, hphi, ht23, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h7, hlam, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                rcases p13736_3 (m.d 0 4) (by simp) with h13747 | h13747
                                                · rcases p13736_3 (m.d 1 4) (by simp) with h13748 | h13748
                                                  · linarith only [h13748, h2, hlam]
                                                  · linarith only [h13674, h13748, hlam]
                                                · linarith only [h13747, hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h2, hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13425, hlam, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13671, hlam, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p13680_1, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h5, hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p13709_1, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13675, hlam, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p13709_1, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13284, h13433, h6, h7, hc12, hc34, hlam, hphi, ht23, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                rcases p13736_3 (m.d 0 4) (by simp) with h13763 | h13763
                                                · linarith only [h13763, h7, hlam]
                                                · linarith only [h13763, h2, hlam]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13425, hc12, hc34, hlam, hphi, ht23, p13736_1]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                rcases p13736_3 (m.d 0 4) (by simp) with h13768 | h13768
                                                · linarith only [h13768, h7, hlam]
                                                · linarith only [h13285, h13768, hlam]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13285, hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13674, hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13678, hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [h13679, hlam, p13736_0]
                                              · have p13736_0 := h13736c.1
                                                have p13736_1 := h13736c.2.1
                                                have p13736_2 := h13736c.2.2.1
                                                have p13736_3 := h13736c.2.2.2
                                                linarith only [hlam, p13736_0]
                                    · linarith only [h13727, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    rcases p13709_3 (m.d 0 2) (by simp) with h13777 | h13777
                                    · rcases p13709_3 (m.d 1 2) (by simp) with h13778 | h13778
                                      · linarith only [h0, h13778, hlam]
                                      · rcases p13709_3 (m.d 2 3) (by simp) with h13780 | h13780
                                        · linarith only [h13780, h4, hlam]
                                        · linarith only [h13677, h13780, hlam]
                                    · linarith only [h13777, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h0, hlam, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13286, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13425, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13433, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h4, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13675, hlam, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13433, h4, h7, hc12, hc34, hlam, hphi, ht23, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h5, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    rcases p13709_3 (m.d 0 2) (by simp) with h13795 | h13795
                                    · rcases p13709_3 (m.d 1 2) (by simp) with h13796 | h13796
                                      · linarith only [h13796, hlam, p13709_0]
                                      · rcases p13709_3 (m.d 2 3) (by simp) with h13798 | h13798
                                        · linarith only [h13675, h13798, hlam]
                                        · linarith only [h13286, h13798, hlam]
                                    · linarith only [h0, h13795, hlam]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13286, hc12, hc24, hlam, hphi, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h0, h13433, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h6, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13284, h6, h7, hc12, hc34, hlam, hphi, ht23, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13677, hlam, p13709_0]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [h13678, hlam, p13709_1]
                                  · have p13709_0 := h13709c.1
                                    have p13709_1 := h13709c.2.1
                                    have p13709_2 := h13709c.2.2.1
                                    have p13709_3 := h13709c.2.2.2
                                    linarith only [hlam, p13709_0]
                                · rcases h2bigk with h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c | h13810c
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    rcases p13810_3 (m.d 0 2) (by simp) with h13812 | h13812
                                    · rcases p13810_3 (m.d 1 2) (by simp) with h13813 | h13813
                                      · linarith only [h0, h13813, hlam]
                                      · rcases p13810_3 (m.d 2 3) (by simp) with h13815 | h13815
                                        · linarith only [h13815, h4, hlam]
                                        · linarith only [h13286, h13815, hlam]
                                    · linarith only [h0, h13812, hlam]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    rcases p13810_3 (m.d 0 2) (by simp) with h13819 | h13819
                                    · rcases p13810_3 (m.d 1 2) (by simp) with h13820 | h13820
                                      · linarith only [h0, h13820, hlam]
                                      · rcases p13810_3 (m.d 2 3) (by simp) with h13822 | h13822
                                        · linarith only [h13822, hlam, p13810_0]
                                        · rcases p13810_3 (m.d 2 4) (by simp) with h13824 | h13824
                                          · linarith only [h13824, h5, hlam]
                                          · linarith only [h13675, h13824, hlam]
                                    · linarith only [h13819, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    rcases p13810_3 (m.d 0 2) (by simp) with h13828 | h13828
                                    · rcases p13810_3 (m.d 1 2) (by simp) with h13829 | h13829
                                      · linarith only [h0, h13829, hlam]
                                      · rcases p13810_3 (m.d 2 3) (by simp) with h13831 | h13831
                                        · linarith only [h13831, h4, hlam]
                                        · rcases p13810_3 (m.d 2 4) (by simp) with h13833 | h13833
                                          · linarith only [h13833, hlam, p13810_0]
                                          · rcases p13810_3 (m.d 2 5) (by simp) with h13835 | h13835
                                            · linarith only [h13835, h6, hlam]
                                            · rcases h4bigk with h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c | h13837c
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                rcases p13837_3 (m.d 0 4) (by simp) with h13839 | h13839
                                                · rcases p13837_3 (m.d 1 4) (by simp) with h13840 | h13840
                                                  · linarith only [h13840, h2, hlam]
                                                  · rcases p13837_3 (m.d 2 4) (by simp) with h13842 | h13842
                                                    · linarith only [h13842, h5, hlam]
                                                    · linarith only [h13425, h13842, hlam]
                                                · linarith only [h13839, h2, hlam]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13433, h13675, h13677, h7, hc12, hc34, hlam, hphi, ht23, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h7, hlam, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                rcases p13837_3 (m.d 0 4) (by simp) with h13848 | h13848
                                                · rcases p13837_3 (m.d 1 4) (by simp) with h13849 | h13849
                                                  · linarith only [h13849, h2, hlam]
                                                  · linarith only [h13674, h13849, hlam]
                                                · linarith only [h13848, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h2, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13425, hlam, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13671, hlam, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p13680_1, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h5, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h0, hlam, p13680_2, p13810_1, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13675, hlam, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p13810_1, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13433, h13677, h4, h7, hc12, hc34, hlam, hphi, ht23, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                rcases p13837_3 (m.d 0 4) (by simp) with h13864 | h13864
                                                · linarith only [h13864, h7, hlam]
                                                · linarith only [h13864, h2, hlam]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13425, hc12, hc34, hlam, hphi, ht23, p13837_1]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                rcases p13837_3 (m.d 0 4) (by simp) with h13869 | h13869
                                                · linarith only [h13869, h7, hlam]
                                                · linarith only [h13285, h13869, hlam]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13285, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13674, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13678, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [h13679, hlam, p13837_0]
                                              · have p13837_0 := h13837c.1
                                                have p13837_1 := h13837c.2.1
                                                have p13837_2 := h13837c.2.2.1
                                                have p13837_3 := h13837c.2.2.2
                                                linarith only [hlam, p13837_0]
                                    · linarith only [h13828, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    rcases p13810_3 (m.d 0 2) (by simp) with h13878 | h13878
                                    · rcases p13810_3 (m.d 1 2) (by simp) with h13879 | h13879
                                      · linarith only [h0, h13879, hlam]
                                      · rcases p13810_3 (m.d 2 3) (by simp) with h13881 | h13881
                                        · linarith only [h13881, h4, hlam]
                                        · linarith only [h13677, h13881, hlam]
                                    · linarith only [h13878, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h0, hlam, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13286, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13425, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13433, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h4, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13675, hlam, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13433, h4, h7, hc12, hc34, hlam, hphi, ht23, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h5, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    rcases p13810_3 (m.d 0 2) (by simp) with h13896 | h13896
                                    · rcases p13810_3 (m.d 1 2) (by simp) with h13897 | h13897
                                      · linarith only [h13897, hlam, p13810_0]
                                      · rcases p13810_3 (m.d 2 3) (by simp) with h13899 | h13899
                                        · linarith only [h13675, h13899, hlam]
                                        · linarith only [h13286, h13899, hlam]
                                    · linarith only [h0, h13896, hlam]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13286, hc12, hc24, hlam, hphi, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h0, h13433, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h6, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13284, h6, h7, hc12, hc34, hlam, hphi, ht23, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13677, hlam, p13810_0]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [h13678, hlam, p13810_1]
                                  · have p13810_0 := h13810c.1
                                    have p13810_1 := h13810c.2.1
                                    have p13810_2 := h13810c.2.2.1
                                    have p13810_3 := h13810c.2.2.2
                                    linarith only [hlam, p13810_0]
                                · rcases h2bigk with h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c | h13911c
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    rcases p13911_3 (m.d 0 2) (by simp) with h13913 | h13913
                                    · rcases p13911_3 (m.d 1 2) (by simp) with h13914 | h13914
                                      · linarith only [h0, h13914, hlam]
                                      · rcases p13911_3 (m.d 2 3) (by simp) with h13916 | h13916
                                        · linarith only [h13916, h4, hlam]
                                        · linarith only [h13286, h13916, hlam]
                                    · linarith only [h0, h13913, hlam]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    rcases p13911_3 (m.d 0 2) (by simp) with h13920 | h13920
                                    · rcases p13911_3 (m.d 1 2) (by simp) with h13921 | h13921
                                      · linarith only [h0, h13921, hlam]
                                      · rcases p13911_3 (m.d 2 3) (by simp) with h13923 | h13923
                                        · linarith only [h13923, hlam, p13911_0]
                                        · rcases p13911_3 (m.d 2 4) (by simp) with h13925 | h13925
                                          · linarith only [h13925, h5, hlam]
                                          · linarith only [h13675, h13925, hlam]
                                    · linarith only [h13920, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    rcases p13911_3 (m.d 0 2) (by simp) with h13929 | h13929
                                    · rcases p13911_3 (m.d 1 2) (by simp) with h13930 | h13930
                                      · linarith only [h0, h13930, hlam]
                                      · rcases p13911_3 (m.d 2 3) (by simp) with h13932 | h13932
                                        · linarith only [h13932, h4, hlam]
                                        · rcases p13911_3 (m.d 2 4) (by simp) with h13934 | h13934
                                          · linarith only [h13934, hlam, p13911_0]
                                          · rcases p13911_3 (m.d 2 5) (by simp) with h13936 | h13936
                                            · linarith only [h13936, h6, hlam]
                                            · rcases h4bigk with h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c | h13938c
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                rcases p13938_3 (m.d 0 4) (by simp) with h13940 | h13940
                                                · rcases p13938_3 (m.d 1 4) (by simp) with h13941 | h13941
                                                  · linarith only [h13941, h2, hlam]
                                                  · rcases p13938_3 (m.d 2 4) (by simp) with h13943 | h13943
                                                    · linarith only [h13943, h5, hlam]
                                                    · linarith only [h13425, h13943, hlam]
                                                · linarith only [h13940, h2, hlam]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13433, h13675, h13677, h7, hc12, hc34, hlam, hphi, ht23, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h7, hlam, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                rcases p13938_3 (m.d 0 4) (by simp) with h13949 | h13949
                                                · rcases p13938_3 (m.d 1 4) (by simp) with h13950 | h13950
                                                  · linarith only [h13950, h2, hlam]
                                                  · linarith only [h13674, h13950, hlam]
                                                · linarith only [h13949, hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h2, hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13425, hlam, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13671, hlam, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p13680_1, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h5, hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p13911_1, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13675, hlam, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p13911_1, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13433, h13677, h4, h7, hc12, hc34, hlam, hphi, ht23, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                rcases p13938_3 (m.d 0 4) (by simp) with h13965 | h13965
                                                · linarith only [h13965, h7, hlam]
                                                · linarith only [h13965, h2, hlam]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13425, hc12, hc34, hlam, hphi, ht23, p13938_1]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                rcases p13938_3 (m.d 0 4) (by simp) with h13970 | h13970
                                                · linarith only [h13970, h7, hlam]
                                                · linarith only [h13285, h13970, hlam]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13285, hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13674, hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13678, hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [h13679, hlam, p13938_0]
                                              · have p13938_0 := h13938c.1
                                                have p13938_1 := h13938c.2.1
                                                have p13938_2 := h13938c.2.2.1
                                                have p13938_3 := h13938c.2.2.2
                                                linarith only [hlam, p13938_0]
                                    · linarith only [h13929, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    rcases p13911_3 (m.d 0 2) (by simp) with h13979 | h13979
                                    · rcases p13911_3 (m.d 1 2) (by simp) with h13980 | h13980
                                      · linarith only [h0, h13980, hlam]
                                      · rcases p13911_3 (m.d 2 3) (by simp) with h13982 | h13982
                                        · linarith only [h13982, h4, hlam]
                                        · linarith only [h13677, h13982, hlam]
                                    · linarith only [h13979, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h0, hlam, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13286, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13425, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13433, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h4, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13675, hlam, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13433, h4, h7, hc12, hc34, hlam, hphi, ht23, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h5, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    rcases p13911_3 (m.d 0 2) (by simp) with h13997 | h13997
                                    · rcases p13911_3 (m.d 1 2) (by simp) with h13998 | h13998
                                      · linarith only [h13998, hlam, p13911_0]
                                      · rcases p13911_3 (m.d 2 3) (by simp) with h14000 | h14000
                                        · linarith only [h13675, h14000, hlam]
                                        · linarith only [h13286, h14000, hlam]
                                    · linarith only [h0, h13997, hlam]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13286, hc12, hc24, hlam, hphi, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h0, h13433, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h6, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13284, h6, h7, hc12, hc34, hlam, hphi, ht23, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13677, hlam, p13911_0]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [h13678, hlam, p13911_1]
                                  · have p13911_0 := h13911c.1
                                    have p13911_1 := h13911c.2.1
                                    have p13911_2 := h13911c.2.2.1
                                    have p13911_3 := h13911c.2.2.2
                                    linarith only [hlam, p13911_0]
                                · rcases h2bigk with h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c | h14012c
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    rcases p14012_3 (m.d 0 2) (by simp) with h14014 | h14014
                                    · rcases p14012_3 (m.d 1 2) (by simp) with h14015 | h14015
                                      · linarith only [h0, h14015, hlam]
                                      · rcases p14012_3 (m.d 2 3) (by simp) with h14017 | h14017
                                        · linarith only [h14017, h4, hlam]
                                        · linarith only [h13286, h14017, hlam]
                                    · linarith only [h0, h14014, hlam]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    rcases p14012_3 (m.d 0 2) (by simp) with h14021 | h14021
                                    · rcases p14012_3 (m.d 1 2) (by simp) with h14022 | h14022
                                      · linarith only [h0, h14022, hlam]
                                      · rcases p14012_3 (m.d 2 3) (by simp) with h14024 | h14024
                                        · linarith only [h14024, hlam, p14012_0]
                                        · rcases p14012_3 (m.d 2 4) (by simp) with h14026 | h14026
                                          · linarith only [h14026, h5, hlam]
                                          · linarith only [h13675, h14026, hlam]
                                    · linarith only [h14021, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    rcases p14012_3 (m.d 0 2) (by simp) with h14030 | h14030
                                    · rcases p14012_3 (m.d 1 2) (by simp) with h14031 | h14031
                                      · linarith only [h0, h14031, hlam]
                                      · rcases p14012_3 (m.d 2 3) (by simp) with h14033 | h14033
                                        · linarith only [h14033, h4, hlam]
                                        · rcases p14012_3 (m.d 2 4) (by simp) with h14035 | h14035
                                          · linarith only [h14035, hlam, p14012_0]
                                          · rcases p14012_3 (m.d 2 5) (by simp) with h14037 | h14037
                                            · linarith only [h14037, h6, hlam]
                                            · rcases h4bigk with h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c | h14039c
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                rcases p14039_3 (m.d 0 4) (by simp) with h14041 | h14041
                                                · rcases p14039_3 (m.d 1 4) (by simp) with h14042 | h14042
                                                  · linarith only [h14042, h2, hlam]
                                                  · rcases p14039_3 (m.d 2 4) (by simp) with h14044 | h14044
                                                    · linarith only [h14044, h5, hlam]
                                                    · linarith only [h13425, h14044, hlam]
                                                · linarith only [h14041, h2, hlam]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13433, h13675, h13677, h7, hc12, hc34, hlam, hphi, ht23, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h7, hlam, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                rcases p14039_3 (m.d 0 4) (by simp) with h14050 | h14050
                                                · rcases p14039_3 (m.d 1 4) (by simp) with h14051 | h14051
                                                  · linarith only [h14051, h2, hlam]
                                                  · linarith only [h13674, h14051, hlam]
                                                · linarith only [h14050, hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h2, hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13425, hlam, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13671, hlam, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p13680_1, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h5, hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p14012_1, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13675, hlam, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p14012_1, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13433, h13677, h4, h7, hc12, hc34, hlam, hphi, ht23, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                rcases p14039_3 (m.d 0 4) (by simp) with h14066 | h14066
                                                · linarith only [h14066, h7, hlam]
                                                · linarith only [h14066, h2, hlam]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13425, hc12, hc34, hlam, hphi, ht23, p14039_1]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                rcases p14039_3 (m.d 0 4) (by simp) with h14071 | h14071
                                                · linarith only [h14071, h7, hlam]
                                                · linarith only [h13285, h14071, hlam]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13285, hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13674, hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13678, hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [h13679, hlam, p14039_0]
                                              · have p14039_0 := h14039c.1
                                                have p14039_1 := h14039c.2.1
                                                have p14039_2 := h14039c.2.2.1
                                                have p14039_3 := h14039c.2.2.2
                                                linarith only [hlam, p14039_0]
                                    · linarith only [h14030, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    rcases p14012_3 (m.d 0 2) (by simp) with h14080 | h14080
                                    · rcases p14012_3 (m.d 1 2) (by simp) with h14081 | h14081
                                      · linarith only [h0, h14081, hlam]
                                      · rcases p14012_3 (m.d 2 3) (by simp) with h14083 | h14083
                                        · linarith only [h14083, h4, hlam]
                                        · linarith only [h13677, h14083, hlam]
                                    · linarith only [h14080, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h0, hlam, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13286, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13425, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13433, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h4, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13675, hlam, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13433, h4, h7, hc12, hc34, hlam, hphi, ht23, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h5, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    rcases p14012_3 (m.d 0 2) (by simp) with h14098 | h14098
                                    · rcases p14012_3 (m.d 1 2) (by simp) with h14099 | h14099
                                      · linarith only [h14099, hlam, p14012_0]
                                      · rcases p14012_3 (m.d 2 3) (by simp) with h14101 | h14101
                                        · linarith only [h13675, h14101, hlam]
                                        · linarith only [h13286, h14101, hlam]
                                    · linarith only [h0, h14098, hlam]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13286, hc12, hc24, hlam, hphi, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h0, h13433, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h6, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13284, h6, h7, hc12, hc34, hlam, hphi, ht23, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13677, hlam, p14012_0]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [h13678, hlam, p14012_1]
                                  · have p14012_0 := h14012c.1
                                    have p14012_1 := h14012c.2.1
                                    have p14012_2 := h14012c.2.2.1
                                    have p14012_3 := h14012c.2.2.2
                                    linarith only [hlam, p14012_0]
                      · linarith only [h13698, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      rcases p13680_3 (m.d 0 1) (by simp) with h14114 | h14114
                      · rcases p13680_3 (m.d 1 2) (by simp) with h14115 | h14115
                        · linarith only [h0, h14115, hlam]
                        · rcases p13680_3 (m.d 1 3) (by simp) with h14117 | h14117
                          · linarith only [h1, h14117, hlam]
                          · linarith only [h13673, h14117, hlam]
                      · linarith only [h14114, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h0, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13286, hlam, p13680_1]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13425, hlam, p13680_1]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13433, hlam, p13680_1]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h1, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h1, h7, hc12, hc34, hlam, hphi, ht23, p13680_1]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13671, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13286, h13433, h4, h7, hc12, hc34, hlam, hphi, ht23, p13680_1]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h2, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      rcases p13680_3 (m.d 0 1) (by simp) with h14132 | h14132
                      · rcases p13680_3 (m.d 1 2) (by simp) with h14133 | h14133
                        · linarith only [h13425, h14133, hlam]
                        · rcases p13680_3 (m.d 1 3) (by simp) with h14135 | h14135
                          · linarith only [h13671, h14135, hlam]
                          · linarith only [h13286, h14135, hlam]
                      · linarith only [h0, h14132, hlam]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13673, h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p13680_1]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      rcases p13680_3 (m.d 0 1) (by simp) with h14141 | h14141
                      · rcases p13680_3 (m.d 1 2) (by simp) with h14142 | h14142
                        · linarith only [h13425, h14142, hlam]
                        · rcases p13680_3 (m.d 1 3) (by simp) with h14144 | h14144
                          · linarith only [h13671, h14144, hlam]
                          · linarith only [h13673, h14144, hlam]
                      · linarith only [h14141, h3, hlam]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h3, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13284, h3, h7, hc12, hc34, hlam, hphi, ht23, p13680_1]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13673, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [h13674, hlam, p13680_0]
                    · have p13680_0 := h13680c.1
                      have p13680_1 := h13680c.2.1
                      have p13680_2 := h13680c.2.2.1
                      have p13680_3 := h13680c.2.2.2
                      linarith only [hlam, p13680_0]
                  · linarith only [h13285, h13679, h7, hlam]
                · linarith only [h13425, h13674, h13678, hlam]
              · linarith only [h1, h13673, h13677, h7, hc23, hc34, hlam, hphi]
          · linarith only [h13671, h13673, h13674, hlam]
        · linarith only [h13284, h13673, h7, hc13, hc34, hlam, hphi]

set_option maxHeartbeats 11350000 in
set_option maxHeartbeats 11350000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x0 (m : N7Model)
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
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13284 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h13285 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h13286 | h13286
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h13284 h13285 h13286
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h13284 h13285 h13286

set_option maxHeartbeats 11350000 in
set_option maxHeartbeats 11350000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x1 (m : N7Model)
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
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13284 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h13285 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  linarith only [h13284, h13285, h7, hlam]

set_option maxHeartbeats 11350000 in
set_option maxHeartbeats 11350000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0 (m : N7Model)
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
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13284 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h13285 | h13285
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h13284 h13285
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h13284 h13285

end R2N4
