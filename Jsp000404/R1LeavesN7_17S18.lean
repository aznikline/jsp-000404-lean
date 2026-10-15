import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9764000 in
set_option maxHeartbeats 9764000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s7_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6421 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h6422 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6423 | h6423
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6424 | h6424
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6425 | h6425
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6426 | h6426
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6427 | h6427
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6428 | h6428
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6429 | h6429
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6430 | h6430
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6431 | h6431
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6432 | h6432
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6433 | h6433
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6434 | h6434
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6435 | h6435
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6436 | h6436
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6437 | h6437
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6438 | h6438
                                · linarith only [h0, h6421, h6430, h6435, h6438, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h6421, h6433, h6434, h6438, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h6421, h6433, h6434, h6437, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h6421, h6428, h6435, h6436, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h6421, h6433, h6435, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6444 | h6444
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6445 | h6445
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6446 | h6446
                              · linarith only [h6431, h6434, h6446, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6448 | h6448
                                · linarith only [h6424, h6434, h6444, h6448, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h0bigk with h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c | h6450c
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, hlam, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, h6421, h6430, h6445, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, h6429, h6431, h6434, h6444, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, h6429, h6431, h6434, h6444, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6421, hlam, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6424, hlam, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6421, h6429, h6431, h6434, h6444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, h6421, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6422, hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6425, hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6427, hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h0, h6422, h6423, h6432, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6423, hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6426, hlam, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6428, hlam, p6450_0]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [h6429, hlam, p6450_1]
                                  · have p6450_0 := h6450c.1
                                    have p6450_1 := h6450c.2.1
                                    have p6450_2 := h6450c.2.2.1
                                    have p6450_3 := h6450c.2.2.2
                                    linarith only [hlam, p6450_0]
                            · linarith only [h0, h6421, h6428, h6444, h6445, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h6421, h6433, h6444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6478 | h6478
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6479 | h6479
                          · linarith only [h6430, h6433, h6479, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6481 | h6481
                            · linarith only [h0, h6421, h6427, h6430, h6433, h6481, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6483 | h6483
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6484 | h6484
                                · rcases h0bigk with h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, hlam, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, h6427, h6430, h6433, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, h6422, h6431, h6483, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, h6428, h6481, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6421, hlam, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6424, hlam, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6421, h6427, h6430, h6433, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h0, h6421, h6428, h6481, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6422, hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6425, hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6427, hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6428, h6481, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6423, hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6426, hlam, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6428, hlam, p6485_0]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [h6429, hlam, p6485_1]
                                  · have p6485_0 := h6485c.1
                                    have p6485_1 := h6485c.2.1
                                    have p6485_2 := h6485c.2.2.1
                                    have p6485_3 := h6485c.2.2.2
                                    linarith only [hlam, p6485_0]
                                · linarith only [h0, h6422, h6430, h6431, h6433, h6483, h6484, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h0, h6421, h6427, h6433, h6478, h6483, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6513 | h6513
                          · linarith only [h6430, h6433, h6513, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6515 | h6515
                            · linarith only [h0, h6421, h6427, h6429, h6430, h6433, h6478, h6515, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6517 | h6517
                              · linarith only [h6431, h6478, h6517, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6519 | h6519
                                · linarith only [h0, h6421, h6427, h6478, h6519, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h6421, h6427, h6429, h6430, h6433, h6519, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6426, h6432, hlam]
                  · linarith only [h0, h6425, h6431, hlam]
                · linarith only [h0, h6424, h6430, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6525 | h6525
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6526 | h6526
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6527 | h6527
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6528 | h6528
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6529 | h6529
                        · linarith only [h0, h6421, h6429, h6528, h6529, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6531 | h6531
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6532 | h6532
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6533 | h6533
                              · linarith only [h6422, h6429, h6526, h6533, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6535 | h6535
                                · linarith only [h6425, h6429, h6531, h6535, hlam]
                                · rcases h0bigk with h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c | h6537c
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, hlam, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, h6422, h6526, h6531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, h6422, h6429, h6526, h6531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, h6427, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    rcases p6537_3 (m.d 0 1) (by simp) with h6546 | h6546
                                    · linarith only [h0, h6546, hlam]
                                    · linarith only [h6422, h6546, hlam]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    rcases p6537_3 (m.d 0 1) (by simp) with h6549 | h6549
                                    · linarith only [h0, h6549, hlam]
                                    · linarith only [h6423, h6549, hlam]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6421, hlam, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6424, hlam, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, h6421, h6422, h6526, h6531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, h6421, h6422, h6429, h6526, h6531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6422, hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6425, hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6427, hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6429, hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6423, hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6426, hlam, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h6428, hlam, p6537_0]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [h0, h6422, h6423, h6526, h6531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6537_1]
                                  · have p6537_0 := h6537c.1
                                    have p6537_1 := h6537c.2.1
                                    have p6537_2 := h6537c.2.2.1
                                    have p6537_3 := h6537c.2.2.2
                                    linarith only [hlam, p6537_0]
                            · linarith only [h0, h6421, h6428, h6531, h6532, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h6421, h6528, h6531, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6569 | h6569
                        · linarith only [h6427, h6429, h6528, h6569, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6571 | h6571
                          · linarith only [h6525, h6528, h6571, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6573 | h6573
                            · linarith only [h0, h6421, h6427, h6525, h6528, h6573, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6575 | h6575
                              · linarith only [h0, h6421, h6427, h6429, h6526, h6528, h6575, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6577 | h6577
                                · linarith only [h6427, h6429, h6577, hlam]
                                · rcases h0bigk with h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c | h6579c
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, hlam, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, h6428, h6528, h6577, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, h6427, h6528, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, h6428, h6528, h6577, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6421, hlam, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6424, hlam, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6421, h6427, h6528, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h0, h6421, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6422, hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6425, hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6427, hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6429, hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6423, hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6426, hlam, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6428, hlam, p6579_0]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [h6427, h6528, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6579_1]
                                  · have p6579_0 := h6579c.1
                                    have p6579_1 := h6579c.2.1
                                    have p6579_2 := h6579c.2.2.1
                                    have p6579_3 := h6579c.2.2.2
                                    linarith only [hlam, p6579_0]
                    · linarith only [h0, h6426, h6527, hlam]
                  · linarith only [h0, h6425, h6526, hlam]
                · linarith only [h0, h6424, h6525, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6608 | h6608
              · linarith only [h6427, h6428, h6608, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6610 | h6610
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6611 | h6611
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6612 | h6612
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6613 | h6613
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6614 | h6614
                        · linarith only [h6422, h6608, h6614, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6616 | h6616
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6617 | h6617
                            · linarith only [h6421, h6428, h6610, h6617, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6619 | h6619
                              · linarith only [h6422, h6608, h6611, h6619, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6621 | h6621
                                · linarith only [h6423, h6608, h6612, h6616, h6617, h6621, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h0bigk with h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c | h6623c
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, hlam, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, h6422, h6611, h6616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, h6421, h6428, h6610, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, h6427, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    rcases p6623_3 (m.d 0 1) (by simp) with h6632 | h6632
                                    · linarith only [h0, h6632, hlam]
                                    · linarith only [h6422, h6632, hlam]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, h6421, h6428, h6610, h6616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6421, hlam, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6424, hlam, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6422, h6428, h6611, h6616, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6428, hlam, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6422, hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6425, hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6427, hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6608, hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6423, hlam, p6623_0]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6426, hlam, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h6421, h6610, h6616, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [h0, h6422, h6423, h6611, h6616, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6623_1]
                                  · have p6623_0 := h6623c.1
                                    have p6623_1 := h6623c.2.1
                                    have p6623_2 := h6623c.2.2.1
                                    have p6623_3 := h6623c.2.2.2
                                    linarith only [hlam, p6623_0]
                          · linarith only [h6427, h6428, h6616, hc23, hc35, hlam, hphi]
                      · linarith only [h6427, h6428, h6613, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h6426, h6612, hlam]
                  · linarith only [h0, h6425, h6611, hlam]
                · linarith only [h0, h6424, h6610, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6656 | h6656
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6657 | h6657
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6658 | h6658
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6659 | h6659
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6660 | h6660
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6661 | h6661
                      · linarith only [h0, h6421, h6427, h6661, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6663 | h6663
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6664 | h6664
                          · linarith only [h6421, h6427, h6658, h6664, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6666 | h6666
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6667 | h6667
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6668 | h6668
                                · rcases h0bigk with h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c | h6669c
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6421, h6658, h6666, h6668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6421, h6427, h6658, h6666, h6668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6421, h6658, h6666, h6668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6421, h6427, h6658, h6666, h6668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    rcases p6669_3 (m.d 0 1) (by simp) with h6679 | h6679
                                    · linarith only [h0, h6679, hlam]
                                    · linarith only [h6423, h6679, hlam]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6421, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6424, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6427, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6423, h6427, h6660, h6666, h6668, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6422, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6425, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6421, h6658, h6666, h6668, hc04, hc45, hlam, hphi, ht0b, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h0, h6422, h6423, h6660, h6666, h6668, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6423, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6426, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6656, hlam, p6669_0]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [h6657, hlam, p6669_1]
                                  · have p6669_0 := h6669c.1
                                    have p6669_1 := h6669c.2.1
                                    have p6669_2 := h6669c.2.2.1
                                    have p6669_3 := h6669c.2.2.2
                                    linarith only [hlam, p6669_0]
                                · linarith only [h6427, h6657, h6668, hlam]
                              · linarith only [h0, h6422, h6663, h6667, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h6427, h6656, h6666, hc23, hc34, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6700 | h6700
                          · linarith only [h0, h6424, h6427, h6656, h6700, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6702 | h6702
                            · linarith only [h0, h6422, h6657, h6658, h6661, h6663, h6702, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h6427, h6656, h6702, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h6426, h6660, hlam]
                  · linarith only [h0, h6425, h6659, hlam]
                · linarith only [h0, h6424, h6658, hlam]
              · linarith only [h6427, h6656, h6657, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6709 | h6709
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6710 | h6710
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6711 | h6711
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6712 | h6712
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6713 | h6713
                      · linarith only [h0, h6421, h6427, h6713, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6715 | h6715
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6716 | h6716
                          · linarith only [h0, h6421, h6422, h6427, h6710, h6715, h6716, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6718 | h6718
                            · linarith only [h6421, h6656, h6710, h6718, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6720 | h6720
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6721 | h6721
                                · rcases h0bigk with h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c | h6722c
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [hlam, p6722_0]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, hlam, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, h6421, h6656, h6709, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, h6421, h6656, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6422, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [hlam, p6722_0]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    rcases p6722_3 (m.d 0 1) (by simp) with h6730 | h6730
                                    · linarith only [h0, h6730, hlam]
                                    · linarith only [h6421, h6730, hlam]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, h6422, h6711, h6720, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    rcases p6722_3 (m.d 0 1) (by simp) with h6734 | h6734
                                    · linarith only [h0, h6734, hlam]
                                    · linarith only [h6423, h6734, hlam]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6421, hlam, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6424, hlam, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [hlam, p6722_0]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6427, hlam, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6656, hlam, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6422, hlam, p6722_0]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6425, hlam, p6722_0]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, h6421, h6422, h6710, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [hlam, p6722_0]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, h6422, h6423, h6712, h6718, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6423, hlam, p6722_0]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6426, hlam, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h0, h6421, h6423, h6710, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [h6709, hlam, p6722_1]
                                  · have p6722_0 := h6722c.1
                                    have p6722_1 := h6722c.2.1
                                    have p6722_2 := h6722c.2.2.1
                                    have p6722_3 := h6722c.2.2.2
                                    linarith only [hlam, p6722_0]
                                · linarith only [h0, h6422, h6427, h6711, h6720, h6721, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h6422, h6715, h6720, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6754 | h6754
                          · linarith only [h6427, h6709, h6710, h6713, h6715, h6754, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6756 | h6756
                            · linarith only [h0, h6422, h6656, h6709, h6710, h6713, h6715, h6756, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6758 | h6758
                              · linarith only [h6711, h6715, h6758, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6760 | h6760
                                · rcases h0bigk with h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c | h6761c
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [hlam, p6761_0]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, hlam, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, h6421, h6710, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, h6709, h6710, h6713, h6715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, h6709, h6710, h6713, h6715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [hlam, p6761_0]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    rcases p6761_3 (m.d 0 1) (by simp) with h6769 | h6769
                                    · linarith only [h0, h6769, hlam]
                                    · linarith only [h6421, h6769, hlam]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, h6709, h6710, h6713, h6715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, h6709, h6710, h6713, h6715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6421, hlam, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6424, hlam, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [hlam, p6761_0]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6427, hlam, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6656, hlam, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6422, hlam, p6761_0]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6425, hlam, p6761_0]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6421, h6427, h6710, hc23, hc34, hlam, hphi, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [hlam, p6761_0]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h0, h6422, h6709, h6710, h6713, h6715, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6423, hlam, p6761_0]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6426, hlam, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6421, h6656, h6710, hc23, hc35, hlam, hphi, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [h6709, hlam, p6761_1]
                                  · have p6761_0 := h6761c.1
                                    have p6761_1 := h6761c.2.1
                                    have p6761_2 := h6761c.2.2.1
                                    have p6761_3 := h6761c.2.2.2
                                    linarith only [hlam, p6761_0]
                                · linarith only [h6427, h6709, h6760, hlam]
                    · linarith only [h0, h6426, h6712, hlam]
                  · linarith only [h0, h6425, h6711, hlam]
                · linarith only [h0, h6424, h6710, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6793 | h6793
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6794 | h6794
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6795 | h6795
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6796 | h6796
                      · linarith only [h0, h6421, h6427, h6796, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6798 | h6798
                        · linarith only [h0, h6422, h6709, h6798, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6800 | h6800
                          · linarith only [h6421, h6427, h6793, h6800, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6802 | h6802
                            · linarith only [h6421, h6656, h6793, h6802, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6804 | h6804
                              · linarith only [h6425, h6709, h6804, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6806 | h6806
                                · rcases h0bigk with h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c | h6807c
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h0, hlam, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h0, h6421, h6793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h0, h6422, h6793, h6796, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h0, h6423, h6793, h6796, h6798, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    rcases p6807_3 (m.d 0 1) (by simp) with h6815 | h6815
                                    · linarith only [h0, h6815, hlam]
                                    · linarith only [h6421, h6815, hlam]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    rcases p6807_3 (m.d 0 1) (by simp) with h6818 | h6818
                                    · linarith only [h0, h6818, hlam]
                                    · linarith only [h6422, h6818, hlam]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    rcases p6807_3 (m.d 0 1) (by simp) with h6821 | h6821
                                    · linarith only [h0, h6821, hlam]
                                    · linarith only [h6423, h6821, hlam]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6421, hlam, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6424, hlam, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6427, hlam, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6656, hlam, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6422, hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6425, hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6421, h6709, h6793, h6806, hc23, hc34, hlam, hphi, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6709, hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6423, hlam, p6807_0]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6426, hlam, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h0, h6421, h6423, h6793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [h6709, h6806, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6807_1]
                                  · have p6807_0 := h6807c.1
                                    have p6807_1 := h6807c.2.1
                                    have p6807_2 := h6807c.2.2.1
                                    have p6807_3 := h6807c.2.2.2
                                    linarith only [hlam, p6807_0]
                                · rcases h0bigk with h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, hlam, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, h6422, h6793, h6796, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    rcases p6839_3 (m.d 0 1) (by simp) with h6847 | h6847
                                    · linarith only [h0, h6847, hlam]
                                    · linarith only [h6421, h6847, hlam]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    rcases p6839_3 (m.d 0 1) (by simp) with h6850 | h6850
                                    · linarith only [h0, h6850, hlam]
                                    · linarith only [h6422, h6850, hlam]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    rcases p6839_3 (m.d 0 1) (by simp) with h6853 | h6853
                                    · linarith only [h0, h6853, hlam]
                                    · linarith only [h6423, h6853, hlam]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6421, hlam, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6424, hlam, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6427, hlam, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6656, hlam, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6422, hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6425, hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, h6421, h6422, h6793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6709, hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6423, hlam, p6839_0]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h6426, hlam, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, h6421, h6423, h6793, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [h0, h6423, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6839_1]
                                  · have p6839_0 := h6839c.1
                                    have p6839_1 := h6839c.2.1
                                    have p6839_2 := h6839c.2.2.1
                                    have p6839_3 := h6839c.2.2.2
                                    linarith only [hlam, p6839_0]
                    · linarith only [h0, h6426, h6795, hlam]
                  · linarith only [h0, h6425, h6794, hlam]
                · linarith only [h0, h6424, h6793, hlam]
        · linarith only [h0, h6423, h6426, hlam]
      · linarith only [h0, h6422, h6425, hlam]
    · linarith only [h0, h6421, h6424, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6877 | h6877
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6878 | h6878
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6879 | h6879
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6880 | h6880
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6881 | h6881
            · linarith only [h6421, h6423, h6881, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6883 | h6883
              · linarith only [h6421, h6423, h6880, h6883, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6885 | h6885
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6886 | h6886
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6887 | h6887
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6888 | h6888
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6889 | h6889
                        · linarith only [h6422, h6423, h6883, h6889, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h6421, h6423, h6888, h6889, hc34, hc45, hlam, hphi]
                      · linarith only [h6880, h6881, h6885, h6888, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h6421, h6879, h6880, h6887, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h6878, h6886, hlam]
                · linarith only [h0, h6877, h6885, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6896 | h6896
            · linarith only [h6422, h6423, h6880, h6896, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6898 | h6898
              · linarith only [h6422, h6423, h6898, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6900 | h6900
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6901 | h6901
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6902 | h6902
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6903 | h6903
                      · linarith only [h6421, h6423, h6880, h6902, h6903, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6905 | h6905
                        · linarith only [h6422, h6423, h6898, h6902, h6905, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6907 | h6907
                          · linarith only [h6421, h6880, h6900, h6907, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6909 | h6909
                            · linarith only [h6421, h6423, h6896, h6900, h6909, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6911 | h6911
                              · linarith only [h0, h6423, h6878, h6905, h6911, hc01, hc12, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6913 | h6913
                                · linarith only [h6422, h6423, h6900, h6903, h6905, h6913, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c | h6915c
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [hlam, p6915_0]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h0, hlam, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6421, h6423, h6900, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6423, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6423, hlam, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [hlam, p6915_0]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    rcases p6915_3 (m.d 0 1) (by simp) with h6923 | h6923
                                    · linarith only [h0, h6923, hlam]
                                    · linarith only [h6421, h6923, hlam]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    rcases p6915_3 (m.d 0 1) (by simp) with h6926 | h6926
                                    · linarith only [h0, h6926, hlam]
                                    · linarith only [h6422, h6926, hlam]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h0, h6422, h6423, h6900, h6903, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6421, hlam, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6877, hlam, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [hlam, p6915_0]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6880, hlam, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6896, hlam, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6422, hlam, p6915_0]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6878, hlam, p6915_0]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h0, h6421, h6422, h6900, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [hlam, p6915_0]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6898, hlam, p6915_0]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6421, h6900, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6879, hlam, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6421, h6423, h6900, h6905, hc23, hc45, hlam, hphi, ht34, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [h6423, h6905, hc04, hc45, hlam, hphi, p6915_1]
                                  · have p6915_0 := h6915c.1
                                    have p6915_1 := h6915c.2.1
                                    have p6915_2 := h6915c.2.2.1
                                    have p6915_3 := h6915c.2.2.2
                                    linarith only [hlam, p6915_0]
                    · linarith only [h0, h6879, h6902, hlam]
                  · linarith only [h0, h6878, h6901, hlam]
                · linarith only [h0, h6877, h6900, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6948 | h6948
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6949 | h6949
            · linarith only [h0, h6421, h6879, h6949, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6951 | h6951
              · linarith only [h0, h6421, h6879, h6948, h6951, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6953 | h6953
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6954 | h6954
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6955 | h6955
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6956 | h6956
                      · linarith only [h0, h6421, h6879, h6955, h6956, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h6421, h6879, h6948, h6953, h6955, h6956, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6959 | h6959
                      · linarith only [h0, h6421, h6955, h6959, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h6948, h6949, h6959, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h6421, h6878, h6879, h6948, h6954, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6877, h6953, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6964 | h6964
            · linarith only [h6422, h6423, h6948, h6964, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6966 | h6966
              · linarith only [h6422, h6423, h6966, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6968 | h6968
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6969 | h6969
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6970 | h6970
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6971 | h6971
                      · linarith only [h0, h6421, h6879, h6948, h6970, h6971, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6973 | h6973
                        · linarith only [h0, h6422, h6879, h6966, h6970, h6973, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6975 | h6975
                          · linarith only [h6421, h6948, h6968, h6975, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6977 | h6977
                            · linarith only [h0, h6421, h6879, h6968, h6970, h6977, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6979 | h6979
                              · linarith only [h0, h6422, h6879, h6969, h6970, h6973, h6979, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6981 | h6981
                                · linarith only [h0, h6422, h6879, h6968, h6970, h6971, h6973, h6981, hc23, hc34, hlam, hphi]
                                · rcases h0bigk with h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c | h6983c
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h0, hlam, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h0, h6421, h6879, h6968, h6970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h0, h6421, h6879, h6948, h6968, h6970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6423, hlam, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6879, h6970, hc01, hc12, hlam, hphi, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6421, h6879, h6968, h6970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6421, h6879, h6948, h6968, h6970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6879, hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6421, hlam, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6877, hlam, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6948, hlam, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6964, hlam, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6422, hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6878, hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h0, h6421, h6422, h6968, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6966, hlam, p6983_0]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6421, h6968, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6879, h6970, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6421, h6879, h6968, h6970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [h6879, h6970, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6983_1]
                                  · have p6983_0 := h6983c.1
                                    have p6983_1 := h6983c.2.1
                                    have p6983_2 := h6983c.2.2.1
                                    have p6983_3 := h6983c.2.2.2
                                    linarith only [hlam, p6983_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7009 | h7009
                      · linarith only [h0, h6421, h6970, h7009, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7011 | h7011
                        · linarith only [h0, h6422, h6966, h6970, h7011, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7013 | h7013
                          · linarith only [h0, h6422, h6948, h6968, h6970, h7009, h7013, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7015 | h7015
                            · linarith only [h0, h6421, h6968, h6970, h7015, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h6422, h6969, h6970, h7013, h7015, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h6422, h6878, h6879, h6969, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6877, h6968, hlam]
      · linarith only [h0, h6422, h6878, hlam]
    · linarith only [h0, h6421, h6877, hlam]

end R2N4
