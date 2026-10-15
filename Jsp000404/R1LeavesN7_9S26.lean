import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16646000 in
set_option maxHeartbeats 16646000 in
theorem r1l7_13_24_L_I_H_I_s8_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h7360 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h7361 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h7362 | h7362
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7363 | h7363
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7364 | h7364
      · rcases m.htr 0 3 4 (by decide) (by decide) with h7365 | h7365
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7366 | h7366
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7367 | h7367
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7368 | h7368
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7369 | h7369
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7370 | h7370
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7371 | h7371
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7372 | h7372
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7373 | h7373
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7374 | h7374
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7375 | h7375
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7376 | h7376
                              · linarith only [h0, h7360, h7368, h7373, h7376, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h7360, h7370, h7372, h7376, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h7360, h7370, h7372, h7375, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h7360, h7371, h7374, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h7360, h7370, h7373, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7382 | h7382
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7383 | h7383
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7384 | h7384
                            · linarith only [h7369, h7372, h7384, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7386 | h7386
                              · linarith only [h7363, h7372, h7382, h7386, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h3bigk with h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c | h7388c
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, h7368, h7383, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, h7383, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  rcases p7388_3 (m.d 0 3) (by simp) with h7392 | h7392
                                  · rcases p7388_3 (m.d 1 3) (by simp) with h7393 | h7393
                                    · linarith only [h7360, h7393, hlam]
                                    · linarith only [h7370, h7393, hlam]
                                  · linarith only [h7392, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  rcases p7388_3 (m.d 0 3) (by simp) with h7397 | h7397
                                  · rcases p7388_3 (m.d 1 3) (by simp) with h7398 | h7398
                                    · linarith only [h7360, h7398, hlam]
                                    · linarith only [h7371, h7398, hlam]
                                  · linarith only [h7397, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7360, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, h7383, h7386, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, h7386, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7363, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7368, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, h7368, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, h7368, h7386, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7365, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7370, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7382, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7386, hlam, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7366, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7371, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h7383, hlam, p7388_0]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [h0, h7360, h7366, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7388_1]
                                · have p7388_0 := h7388c.1
                                  have p7388_1 := h7388c.2.1
                                  have p7388_2 := h7388c.2.2.1
                                  have p7388_3 := h7388c.2.2.2
                                  linarith only [hlam, p7388_0]
                          · linarith only [h0, h7360, h7371, h7383, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h7360, h7370, h7382, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h7360, h7366, h7370, h7371, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7425 | h7425
                    · linarith only [h0, h7360, h7365, h7370, h7425, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7427 | h7427
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7428 | h7428
                        · linarith only [h7368, h7370, h7428, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7430 | h7430
                          · linarith only [h7368, h7425, h7430, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7432 | h7432
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7433 | h7433
                              · rcases h3bigk with h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c | h7434c
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  rcases p7434_3 (m.d 0 3) (by simp) with h7436 | h7436
                                  · rcases p7434_3 (m.d 1 3) (by simp) with h7437 | h7437
                                    · linarith only [h7360, h7437, hlam]
                                    · rcases p7434_3 (m.d 2 3) (by simp) with h7439 | h7439
                                      · linarith only [h7363, h7439, hlam]
                                      · rcases p7434_3 (m.d 3 4) (by simp) with h7441 | h7441
                                        · linarith only [h7365, h7441, hlam]
                                        · linarith only [h7370, h7441, hlam]
                                  · linarith only [h7360, h7436, hlam]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  rcases p7434_3 (m.d 0 3) (by simp) with h7445 | h7445
                                  · rcases p7434_3 (m.d 1 3) (by simp) with h7446 | h7446
                                    · linarith only [h7360, h7446, hlam]
                                    · linarith only [h7368, h7446, hlam]
                                  · linarith only [h7363, h7445, hlam]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h0, h7360, h7425, h7433, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h0, h7360, h7368, h7425, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7360, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7425, h7433, hc23, hc34, hlam, hphi, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7370, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7425, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7363, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7368, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7428, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7430, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7365, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h0, h7360, h7365, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h0, h7360, h7365, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h0, h7360, h7365, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7366, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h0, h7360, h7366, h7368, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h0, h7360, h7366, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7434_1]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [h7433, hlam, p7434_0]
                                · have p7434_0 := h7434c.1
                                  have p7434_1 := h7434c.2.1
                                  have p7434_2 := h7434c.2.2.1
                                  have p7434_3 := h7434c.2.2.2
                                  linarith only [hlam, p7434_0]
                              · linarith only [h0, h7361, h7369, h7432, h7433, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h7360, h7365, h7370, h7427, h7432, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7474 | h7474
                        · linarith only [h7368, h7370, h7474, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7476 | h7476
                          · linarith only [h0, h7360, h7365, h7367, h7368, h7370, h7427, h7476, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7478 | h7478
                            · linarith only [h7369, h7427, h7478, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7480 | h7480
                              · linarith only [h0, h7360, h7365, h7427, h7480, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h7360, h7365, h7367, h7368, h7370, h7480, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h7364, h7369, hlam]
              · linarith only [h0, h7363, h7368, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7485 | h7485
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7486 | h7486
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7487 | h7487
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7488 | h7488
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7489 | h7489
                      · linarith only [h0, h7361, h7367, h7489, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7491 | h7491
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7492 | h7492
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7493 | h7493
                            · linarith only [h7361, h7367, h7486, h7493, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7495 | h7495
                              · linarith only [h7361, h7367, h7486, h7491, h7495, hlam]
                              · rcases h3bigk with h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c | h7497c
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, h7485, h7492, h7495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, h7492, h7495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  rcases p7497_3 (m.d 0 3) (by simp) with h7501 | h7501
                                  · rcases p7497_3 (m.d 1 3) (by simp) with h7502 | h7502
                                    · linarith only [h7360, h7502, hlam]
                                    · linarith only [h7487, h7502, hlam]
                                  · linarith only [h7501, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  rcases p7497_3 (m.d 0 3) (by simp) with h7506 | h7506
                                  · rcases p7497_3 (m.d 1 3) (by simp) with h7507 | h7507
                                    · linarith only [h7360, h7507, hlam]
                                    · linarith only [h7488, h7507, hlam]
                                  · linarith only [h7506, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7360, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, h7492, h7495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, h7495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7363, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7485, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, h7485, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, h7485, h7495, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7365, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7487, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7491, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7495, hlam, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7366, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7488, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h7492, hlam, p7497_0]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [h0, h7360, h7366, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7497_1]
                                · have p7497_0 := h7497c.1
                                  have p7497_1 := h7497c.2.1
                                  have p7497_2 := h7497c.2.2.1
                                  have p7497_3 := h7497c.2.2.2
                                  linarith only [hlam, p7497_0]
                          · linarith only [h0, h7360, h7488, h7492, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h7360, h7487, h7491, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h7360, h7366, h7487, h7488, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7534 | h7534
                    · linarith only [h0, h7360, h7365, h7487, h7534, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7536 | h7536
                      · linarith only [h0, h7361, h7367, h7536, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7538 | h7538
                        · linarith only [h7485, h7487, h7538, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7540 | h7540
                          · linarith only [h7485, h7534, h7540, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7542 | h7542
                            · linarith only [h0, h7364, h7365, h7367, h7487, h7542, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7544 | h7544
                              · linarith only [h7365, h7367, h7544, hlam]
                              · rcases h3bigk with h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c | h7546c
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  rcases p7546_3 (m.d 0 3) (by simp) with h7548 | h7548
                                  · rcases p7546_3 (m.d 1 3) (by simp) with h7549 | h7549
                                    · linarith only [h7360, h7549, hlam]
                                    · rcases p7546_3 (m.d 2 3) (by simp) with h7551 | h7551
                                      · linarith only [h7363, h7551, hlam]
                                      · rcases p7546_3 (m.d 3 4) (by simp) with h7553 | h7553
                                        · linarith only [h7365, h7553, hlam]
                                        · linarith only [h7487, h7553, hlam]
                                  · linarith only [h7360, h7548, hlam]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  rcases p7546_3 (m.d 0 3) (by simp) with h7557 | h7557
                                  · rcases p7546_3 (m.d 1 3) (by simp) with h7558 | h7558
                                    · linarith only [h7360, h7558, hlam]
                                    · linarith only [h7485, h7558, hlam]
                                  · linarith only [h7363, h7557, hlam]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h0, h7360, h7485, h7487, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h0, h7360, h7485, h7487, h7544, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7360, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7487, hc23, hc34, hlam, hphi, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7487, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7534, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7363, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7485, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7538, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7540, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7365, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h0, h7360, h7365, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h0, h7360, h7366, h7544, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7544, hlam, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h7366, hlam, p7546_0]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h0, h7360, h7366, h7485, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h0, h7360, h7366, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [h0, h7360, h7366, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7546_1]
                                · have p7546_0 := h7546c.1
                                  have p7546_1 := h7546c.2.1
                                  have p7546_2 := h7546c.2.2.1
                                  have p7546_3 := h7546c.2.2.2
                                  linarith only [hlam, p7546_0]
                · linarith only [h0, h7364, h7486, hlam]
              · linarith only [h0, h7363, h7485, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7586 | h7586
            · linarith only [h7365, h7366, h7586, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7588 | h7588
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7589 | h7589
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7590 | h7590
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7591 | h7591
                    · linarith only [h0, h7360, h7366, h7591, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7593 | h7593
                      · linarith only [h7362, h7586, h7590, h7591, h7593, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7595 | h7595
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7596 | h7596
                          · linarith only [h7360, h7366, h7588, h7596, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7598 | h7598
                            · linarith only [h0, h7362, h7586, h7589, h7590, h7591, h7598, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7600 | h7600
                              · linarith only [h0, h7362, h7586, h7588, h7591, h7595, h7600, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h3bigk with h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c | h7602c
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7366, hc13, hc35, hlam, hphi, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7366, h7600, hc23, hc45, hlam, hphi, ht34, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7366, h7600, hc34, hc45, hlam, hphi, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7366, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7360, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h0, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h0, h7360, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7591, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7363, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7588, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7363, h7366, h7600, hc34, hc45, hlam, hphi, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7596, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7365, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7590, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7595, hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [hlam, p7602_0]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7600, hlam, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7365, h7600, hc34, hc45, hlam, hphi, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7590, h7600, hc34, hc45, hlam, hphi, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [h7595, h7600, hc34, hc45, hlam, hphi, p7602_1]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  rcases p7602_3 (m.d 0 3) (by simp) with h7626 | h7626
                                  · linarith only [h7366, h7626, hlam]
                                  · linarith only [h7365, h7626, hlam]
                                · have p7602_0 := h7602c.1
                                  have p7602_1 := h7602c.2.1
                                  have p7602_2 := h7602c.2.2.1
                                  have p7602_3 := h7602c.2.2.2
                                  linarith only [hlam, p7602_0]
                        · linarith only [h7365, h7366, h7595, hc23, hc35, hlam, hphi]
                  · linarith only [h7365, h7366, h7590, hc13, hc35, hlam, hphi]
                · linarith only [h0, h7364, h7589, hlam]
              · linarith only [h0, h7363, h7588, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h7634 | h7634
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7635 | h7635
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7636 | h7636
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7637 | h7637
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7638 | h7638
                  · linarith only [h0, h7360, h7365, h7638, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7640 | h7640
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7641 | h7641
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7642 | h7642
                        · linarith only [h7360, h7365, h7636, h7642, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7644 | h7644
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7645 | h7645
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7646 | h7646
                              · rcases h3bigk with h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c | h7647c
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7365, h7636, h7644, h7646, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7647_1]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7365, h7644, h7646, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7647_1]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7365, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  rcases p7647_3 (m.d 0 3) (by simp) with h7652 | h7652
                                  · rcases p7647_3 (m.d 1 3) (by simp) with h7653 | h7653
                                    · linarith only [h7360, h7653, hlam]
                                    · linarith only [h7640, h7653, hlam]
                                  · linarith only [h7652, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7360, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h0, h7360, h7644, h7646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7647_1]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7638, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h0, h7361, h7638, h7646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7647_1]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7363, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7636, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7642, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h0, h7361, h7636, h7638, h7646, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7647_1]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  rcases p7647_3 (m.d 0 3) (by simp) with h7667 | h7667
                                  · linarith only [h7667, hlam, p7647_0]
                                  · rcases p7647_3 (m.d 1 3) (by simp) with h7669 | h7669
                                    · linarith only [h7638, h7669, hlam]
                                    · rcases p7647_3 (m.d 2 3) (by simp) with h7671 | h7671
                                      · linarith only [h7642, h7671, hlam]
                                      · rcases p7647_3 (m.d 3 4) (by simp) with h7673 | h7673
                                        · rcases p7647_3 (m.d 3 5) (by simp) with h7674 | h7674
                                          · linarith only [h7646, h7674, hlam]
                                          · rcases h4bigk with h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c | h7676c
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h0, h7361, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h0, h7361, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7365, hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h0, h7361, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7361, hlam, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h0, h7361, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7638, hlam, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h0, h7361, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7364, hlam, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7637, hlam, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7642, hlam, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h0, h7364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7365, hc03, hc34, hlam, hphi, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7636, h7638, hc23, hc34, hlam, hphi, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7642, hc23, hc34, hlam, hphi, p7676_1]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              rcases p7676_3 (m.d 0 4) (by simp) with h7696 | h7696
                                              · linarith only [h7365, h7696, hlam]
                                              · linarith only [h7635, h7696, hlam]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7635, hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7641, hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7645, hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [h7646, hlam, p7676_0]
                                            · have p7676_0 := h7676c.1
                                              have p7676_1 := h7676c.2.1
                                              have p7676_2 := h7676c.2.2.1
                                              have p7676_3 := h7676c.2.2.2
                                              linarith only [hlam, p7676_0]
                                        · linarith only [h7673, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  rcases p7647_3 (m.d 0 3) (by simp) with h7705 | h7705
                                  · linarith only [h7365, h7705, hlam]
                                  · linarith only [h7360, h7705, hlam]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  rcases p7647_3 (m.d 0 3) (by simp) with h7708 | h7708
                                  · linarith only [h7365, h7708, hlam]
                                  · linarith only [h7363, h7708, hlam]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  rcases p7647_3 (m.d 0 3) (by simp) with h7712 | h7712
                                  · linarith only [h7365, h7712, hlam]
                                  · linarith only [h7634, h7712, hlam]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7634, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7640, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7644, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [h7646, hlam, p7647_0]
                                · have p7647_0 := h7647c.1
                                  have p7647_1 := h7647c.2.1
                                  have p7647_2 := h7647c.2.2.1
                                  have p7647_3 := h7647c.2.2.2
                                  linarith only [hlam, p7647_0]
                              · linarith only [h0, h7360, h7361, h7365, h7635, h7636, h7644, h7646, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h7361, h7641, h7642, h7644, h7645, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h7365, h7634, h7644, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h7361, h7635, h7638, h7640, h7641, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h7365, h7634, h7640, hc13, hc34, hlam, hphi]
                · linarith only [h0, h7364, h7637, hlam]
              · linarith only [h0, h7363, h7636, hlam]
            · linarith only [h7365, h7634, h7635, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h7728 | h7728
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7729 | h7729
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7730 | h7730
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7731 | h7731
                  · linarith only [h0, h7360, h7365, h7731, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7733 | h7733
                    · linarith only [h7360, h7634, h7733, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7735 | h7735
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7736 | h7736
                        · linarith only [h7363, h7365, h7736, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7738 | h7738
                          · linarith only [h7363, h7634, h7738, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7740 | h7740
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7741 | h7741
                              · rcases h3bigk with h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c | h7742c
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7634, h7729, h7741, hc23, hc34, hlam, hphi, p7742_1]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7634, h7741, hc23, hc34, hlam, hphi, p7742_1]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7365, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7634, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7360, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h0, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7742_1]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7731, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7733, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7363, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7729, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7736, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7738, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  rcases p7742_3 (m.d 0 3) (by simp) with h7758 | h7758
                                  · linarith only [h7758, hlam, p7742_0]
                                  · rcases p7742_3 (m.d 1 3) (by simp) with h7760 | h7760
                                    · linarith only [h7731, h7760, hlam]
                                    · rcases p7742_3 (m.d 2 3) (by simp) with h7762 | h7762
                                      · linarith only [h7736, h7762, hlam]
                                      · rcases p7742_3 (m.d 3 4) (by simp) with h7764 | h7764
                                        · rcases p7742_3 (m.d 3 5) (by simp) with h7765 | h7765
                                          · linarith only [h7741, h7765, hlam]
                                          · linarith only [h7634, h7765, hlam]
                                        · linarith only [h7764, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  rcases p7742_3 (m.d 0 3) (by simp) with h7769 | h7769
                                  · linarith only [h7365, h7769, hlam]
                                  · linarith only [h7360, h7769, hlam]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  rcases p7742_3 (m.d 0 3) (by simp) with h7772 | h7772
                                  · linarith only [h7365, h7772, hlam]
                                  · linarith only [h7363, h7772, hlam]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7634, hc03, hc34, hlam, hphi, p7742_1]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  rcases p7742_3 (m.d 0 3) (by simp) with h7777 | h7777
                                  · linarith only [h7777, hlam, p7742_0]
                                  · rcases p7742_3 (m.d 1 3) (by simp) with h7779 | h7779
                                    · linarith only [h7733, h7779, hlam]
                                    · rcases p7742_3 (m.d 2 3) (by simp) with h7781 | h7781
                                      · linarith only [h7738, h7781, hlam]
                                      · rcases p7742_3 (m.d 3 4) (by simp) with h7783 | h7783
                                        · rcases p7742_3 (m.d 3 5) (by simp) with h7784 | h7784
                                          · rcases h4bigk with h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c | h7785c
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7730, h7740, hc04, hc45, hlam, hphi, ht0b, ht5b, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h0, h7361, h7740, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7365, hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h0, h7361, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7361, hlam, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7740, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7731, hlam, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h0, h7361, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7364, hlam, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7730, hlam, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7736, hlam, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h0, h7364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7360, h7365, h7729, hc23, hc34, hlam, hphi, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7729, h7731, hc23, hc34, hlam, hphi, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7736, hc23, hc34, hlam, hphi, p7785_1]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              rcases p7785_3 (m.d 0 4) (by simp) with h7805 | h7805
                                              · linarith only [h7365, h7805, hlam]
                                              · linarith only [h7728, h7805, hlam]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7728, hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7735, hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7740, hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [h7741, hlam, p7785_0]
                                            · have p7785_0 := h7785c.1
                                              have p7785_1 := h7785c.2.1
                                              have p7785_2 := h7785c.2.2.1
                                              have p7785_3 := h7785c.2.2.2
                                              linarith only [hlam, p7785_0]
                                          · linarith only [h7784, hlam, p7742_0]
                                        · linarith only [h7365, h7783, hlam]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  rcases p7742_3 (m.d 0 3) (by simp) with h7815 | h7815
                                  · linarith only [h7634, h7815, hlam]
                                  · linarith only [h7360, h7815, hlam]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  rcases p7742_3 (m.d 0 3) (by simp) with h7818 | h7818
                                  · linarith only [h7634, h7818, hlam]
                                  · linarith only [h7363, h7818, hlam]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [h7741, hlam, p7742_0]
                                · have p7742_0 := h7742c.1
                                  have p7742_1 := h7742c.2.1
                                  have p7742_2 := h7742c.2.2.1
                                  have p7742_3 := h7742c.2.2.2
                                  linarith only [hlam, p7742_0]
                              · linarith only [h0, h7361, h7730, h7740, h7741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h7361, h7735, h7740, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7825 | h7825
                        · linarith only [h0, h7360, h7365, h7728, h7729, h7735, h7825, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7827 | h7827
                          · linarith only [h0, h7361, h7634, h7728, h7729, h7731, h7735, h7827, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7829 | h7829
                            · linarith only [h7730, h7735, h7829, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7831 | h7831
                              · rcases h3bigk with h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c | h7832c
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7365, h7729, hc23, hc34, hlam, hphi, p7832_1]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7365, hc23, hc34, hlam, hphi, p7832_1]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7365, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7634, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7360, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h0, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7832_1]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7731, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7733, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7363, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7729, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7825, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7827, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  rcases p7832_3 (m.d 0 3) (by simp) with h7848 | h7848
                                  · linarith only [h7848, hlam, p7832_0]
                                  · rcases p7832_3 (m.d 1 3) (by simp) with h7850 | h7850
                                    · linarith only [h7731, h7850, hlam]
                                    · rcases p7832_3 (m.d 2 3) (by simp) with h7852 | h7852
                                      · linarith only [h7825, h7852, hlam]
                                      · rcases p7832_3 (m.d 3 4) (by simp) with h7854 | h7854
                                        · rcases p7832_3 (m.d 3 5) (by simp) with h7855 | h7855
                                          · linarith only [h7831, h7855, hlam]
                                          · linarith only [h7634, h7855, hlam]
                                        · linarith only [h7854, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  rcases p7832_3 (m.d 0 3) (by simp) with h7859 | h7859
                                  · linarith only [h7365, h7859, hlam]
                                  · linarith only [h7360, h7859, hlam]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  rcases p7832_3 (m.d 0 3) (by simp) with h7862 | h7862
                                  · linarith only [h7365, h7862, hlam]
                                  · linarith only [h7363, h7862, hlam]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7634, hc03, hc34, hlam, hphi, p7832_1]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  rcases p7832_3 (m.d 0 3) (by simp) with h7867 | h7867
                                  · linarith only [h7867, hlam, p7832_0]
                                  · rcases p7832_3 (m.d 1 3) (by simp) with h7869 | h7869
                                    · linarith only [h7733, h7869, hlam]
                                    · rcases p7832_3 (m.d 2 3) (by simp) with h7871 | h7871
                                      · linarith only [h7827, h7871, hlam]
                                      · rcases p7832_3 (m.d 3 4) (by simp) with h7873 | h7873
                                        · rcases p7832_3 (m.d 3 5) (by simp) with h7874 | h7874
                                          · rcases h4bigk with h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c | h7875c
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h0, h7361, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h0, h7361, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7365, hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h0, h7361, h7735, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7361, hlam, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h0, h7361, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7731, hlam, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7735, hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7364, hlam, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7730, hlam, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7825, hlam, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7829, hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7360, h7365, h7729, hc23, hc34, hlam, hphi, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7729, h7731, hc23, hc34, hlam, hphi, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7825, hc23, hc34, hlam, hphi, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7729, h7731, h7735, hc23, hc34, hlam, hphi, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7728, hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7728, h7729, h7731, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h0, h7361, h7728, h7825, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7875_1]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [h7831, hlam, p7875_0]
                                            · have p7875_0 := h7875c.1
                                              have p7875_1 := h7875c.2.1
                                              have p7875_2 := h7875c.2.2.1
                                              have p7875_3 := h7875c.2.2.2
                                              linarith only [hlam, p7875_0]
                                          · linarith only [h7874, hlam, p7832_0]
                                        · linarith only [h7365, h7873, hlam]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  rcases p7832_3 (m.d 0 3) (by simp) with h7903 | h7903
                                  · linarith only [h7634, h7903, hlam]
                                  · linarith only [h7360, h7903, hlam]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  rcases p7832_3 (m.d 0 3) (by simp) with h7906 | h7906
                                  · linarith only [h7634, h7906, hlam]
                                  · linarith only [h7363, h7906, hlam]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [h7831, hlam, p7832_0]
                                · have p7832_0 := h7832c.1
                                  have p7832_1 := h7832c.2.1
                                  have p7832_2 := h7832c.2.2.1
                                  have p7832_3 := h7832c.2.2.2
                                  linarith only [hlam, p7832_0]
                              · linarith only [h0, h7360, h7361, h7365, h7728, h7729, h7831, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h7364, h7730, hlam]
              · linarith only [h0, h7363, h7729, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h7914 | h7914
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7915 | h7915
                · rcases m.htr 1 3 4 (by decide) (by decide) with h7916 | h7916
                  · linarith only [h7360, h7365, h7916, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h7918 | h7918
                    · linarith only [h7360, h7634, h7918, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h7920 | h7920
                      · linarith only [h0, h7361, h7728, h7920, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h7922 | h7922
                        · linarith only [h7360, h7365, h7914, h7922, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h7924 | h7924
                          · linarith only [h7360, h7634, h7914, h7924, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h7926 | h7926
                            · linarith only [h7361, h7728, h7915, h7926, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h7928 | h7928
                              · rcases h3bigk with h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7365, hc13, hc34, hlam, hphi, p7929_1]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7365, hc23, hc34, hlam, hphi, p7929_1]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7365, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7634, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7360, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7361, h7728, h7916, h7928, hc23, hc35, hlam, hphi, p7929_1]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7916, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7918, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7363, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7914, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7922, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7924, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  rcases p7929_3 (m.d 0 3) (by simp) with h7945 | h7945
                                  · linarith only [h7945, hlam, p7929_0]
                                  · rcases p7929_3 (m.d 1 3) (by simp) with h7947 | h7947
                                    · linarith only [h7916, h7947, hlam]
                                    · rcases p7929_3 (m.d 2 3) (by simp) with h7949 | h7949
                                      · linarith only [h7922, h7949, hlam]
                                      · rcases p7929_3 (m.d 3 4) (by simp) with h7951 | h7951
                                        · rcases p7929_3 (m.d 3 5) (by simp) with h7952 | h7952
                                          · linarith only [h7928, h7952, hlam]
                                          · linarith only [h7634, h7952, hlam]
                                        · linarith only [h7951, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  rcases p7929_3 (m.d 0 3) (by simp) with h7956 | h7956
                                  · linarith only [h7365, h7956, hlam]
                                  · linarith only [h7360, h7956, hlam]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  rcases p7929_3 (m.d 0 3) (by simp) with h7959 | h7959
                                  · linarith only [h7365, h7959, hlam]
                                  · linarith only [h7363, h7959, hlam]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7365, h7728, h7928, hc03, hc34, hlam, hphi, p7929_1]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  rcases p7929_3 (m.d 0 3) (by simp) with h7964 | h7964
                                  · linarith only [h7964, hlam, p7929_0]
                                  · rcases p7929_3 (m.d 1 3) (by simp) with h7966 | h7966
                                    · linarith only [h7918, h7966, hlam]
                                    · rcases p7929_3 (m.d 2 3) (by simp) with h7968 | h7968
                                      · linarith only [h7924, h7968, hlam]
                                      · rcases p7929_3 (m.d 3 4) (by simp) with h7970 | h7970
                                        · rcases p7929_3 (m.d 3 5) (by simp) with h7971 | h7971
                                          · rcases h4bigk with h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c | h7972c
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7728, h7915, hc24, hc45, hlam, hphi, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h0, h7362, h7728, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7365, hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7728, hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7361, hlam, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h0, h7361, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7916, hlam, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7920, hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7364, hlam, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7915, hlam, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7922, hlam, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7926, hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7360, h7365, h7914, hc23, hc34, hlam, hphi, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7914, h7916, hc23, hc34, hlam, hphi, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7922, hc23, hc34, hlam, hphi, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7360, h7365, h7728, h7914, hc23, hc34, hlam, hphi, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7360, h7365, h7914, hc23, hc45, hlam, hphi, ht34, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7914, h7916, hc23, hc45, hlam, hphi, ht34, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7922, hc23, hc45, hlam, hphi, ht34, p7972_1]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [h7928, hlam, p7972_0]
                                            · have p7972_0 := h7972c.1
                                              have p7972_1 := h7972c.2.1
                                              have p7972_2 := h7972c.2.2.1
                                              have p7972_3 := h7972c.2.2.2
                                              linarith only [hlam, p7972_0]
                                          · linarith only [h7971, hlam, p7929_0]
                                        · linarith only [h7365, h7970, hlam]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  rcases p7929_3 (m.d 0 3) (by simp) with h8000 | h8000
                                  · linarith only [h7634, h8000, hlam]
                                  · linarith only [h7360, h8000, hlam]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  rcases p7929_3 (m.d 0 3) (by simp) with h8003 | h8003
                                  · linarith only [h7634, h8003, hlam]
                                  · linarith only [h7363, h8003, hlam]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [h7928, hlam, p7929_0]
                                · have p7929_0 := h7929c.1
                                  have p7929_1 := h7929c.2.1
                                  have p7929_2 := h7929c.2.2.1
                                  have p7929_3 := h7929c.2.2.2
                                  linarith only [hlam, p7929_0]
                              · rcases h3bigk with h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c | h8008c
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7365, h7914, hc23, hc34, hlam, hphi, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7365, hc23, hc34, hlam, hphi, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7365, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7634, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7360, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h0, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7916, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7918, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7363, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7914, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7922, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7924, hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7928, hc03, hc45, hlam, hphi, ht34, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7914, h7928, hc23, hc45, hlam, hphi, ht34, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7928, hc23, hc45, hlam, hphi, ht34, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [hlam, p8008_0]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7928, hlam, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  rcases p8008_3 (m.d 0 3) (by simp) with h8029 | h8029
                                  · linarith only [h8029, hlam, p8008_0]
                                  · rcases p8008_3 (m.d 1 3) (by simp) with h8031 | h8031
                                    · linarith only [h7918, h8031, hlam]
                                    · rcases p8008_3 (m.d 2 3) (by simp) with h8033 | h8033
                                      · linarith only [h7924, h8033, hlam]
                                      · rcases p8008_3 (m.d 3 4) (by simp) with h8035 | h8035
                                        · linarith only [h7928, h8035, hlam]
                                        · linarith only [h7365, h8035, hlam]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  rcases p8008_3 (m.d 0 3) (by simp) with h8038 | h8038
                                  · linarith only [h7634, h8038, hlam]
                                  · linarith only [h7360, h8038, hlam]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  rcases p8008_3 (m.d 0 3) (by simp) with h8041 | h8041
                                  · linarith only [h7634, h8041, hlam]
                                  · linarith only [h7363, h8041, hlam]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [h7360, h7365, h7914, h7928, hc23, hc45, hlam, hphi, ht34, p8008_1]
                                · have p8008_0 := h8008c.1
                                  have p8008_1 := h8008c.2.1
                                  have p8008_2 := h8008c.2.2.1
                                  have p8008_3 := h8008c.2.2.2
                                  linarith only [hlam, p8008_0]
                · linarith only [h0, h7364, h7915, hlam]
              · linarith only [h0, h7363, h7914, hlam]
      · linarith only [h0, h7361, h7364, hlam]
    · linarith only [h0, h7360, h7363, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8050 | h8050
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8051 | h8051
      · rcases m.htr 0 3 4 (by decide) (by decide) with h8052 | h8052
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8053 | h8053
          · linarith only [h7360, h7362, h8053, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8055 | h8055
            · linarith only [h7360, h7362, h8052, h8055, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8057 | h8057
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8058 | h8058
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8059 | h8059
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8060 | h8060
                    · linarith only [h0, h7360, h8053, h8060, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8062 | h8062
                      · linarith only [h7360, h7362, h8055, h8059, h8062, hlam]
                      · linarith only [h7360, h7362, h8059, h8062, hc34, hc45, hlam, hphi]
                  · linarith only [h8052, h8053, h8057, h8059, hc23, hc35, hlam, hphi]
                · linarith only [h0, h7360, h8051, h8052, h8058, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h8050, h8057, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h8068 | h8068
          · linarith only [h7361, h7362, h8052, h8068, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h8070 | h8070
            · linarith only [h7361, h7362, h8070, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h8072 | h8072
              · rcases m.htr 1 2 4 (by decide) (by decide) with h8073 | h8073
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8074 | h8074
                  · linarith only [h7360, h7362, h8052, h8074, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8076 | h8076
                    · linarith only [h7360, h7362, h8068, h8076, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8078 | h8078
                      · linarith only [h7361, h7362, h8052, h8070, h8076, h8078, hc03, hc35, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8080 | h8080
                        · linarith only [h7360, h7362, h8072, h8078, h8080, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8082 | h8082
                          · linarith only [h7360, h8068, h8072, h8082, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8084 | h8084
                            · linarith only [h7361, h7362, h8073, h8078, h8084, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8086 | h8086
                              · linarith only [h7361, h7362, h8072, h8074, h8078, h8086, hc23, hc34, hlam, hphi]
                              · rcases h3bigk with h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c | h8088c
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h7360, h7362, h8072, h8076, hc23, hc35, hlam, hphi, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h7361, h7362, h8052, h8076, hc23, hc35, hlam, hphi, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8052, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8068, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h7360, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h7360, h7362, h8076, hc23, hc35, hlam, hphi, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8074, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8076, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8050, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8072, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8080, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8082, hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8086, hc03, hc45, hlam, hphi, ht34, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8072, h8086, hc23, hc45, hlam, hphi, ht34, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8086, hc23, hc45, hlam, hphi, ht34, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [hlam, p8088_0]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h8086, hlam, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  rcases p8088_3 (m.d 0 3) (by simp) with h8109 | h8109
                                  · linarith only [h8109, hlam, p8088_0]
                                  · rcases p8088_3 (m.d 1 3) (by simp) with h8111 | h8111
                                    · linarith only [h8076, h8111, hlam]
                                    · rcases p8088_3 (m.d 2 3) (by simp) with h8113 | h8113
                                      · linarith only [h8082, h8113, hlam]
                                      · rcases p8088_3 (m.d 3 4) (by simp) with h8115 | h8115
                                        · linarith only [h8086, h8115, hlam]
                                        · linarith only [h8052, h8115, hlam]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  rcases p8088_3 (m.d 0 3) (by simp) with h8118 | h8118
                                  · linarith only [h8068, h8118, hlam]
                                  · linarith only [h7360, h8118, hlam]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  rcases p8088_3 (m.d 0 3) (by simp) with h8121 | h8121
                                  · linarith only [h8068, h8121, hlam]
                                  · linarith only [h8050, h8121, hlam]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [h7360, h8052, h8072, h8086, hc23, hc45, hlam, hphi, ht34, p8088_1]
                                · have p8088_0 := h8088c.1
                                  have p8088_1 := h8088c.2.1
                                  have p8088_2 := h8088c.2.2.1
                                  have p8088_3 := h8088c.2.2.2
                                  linarith only [hlam, p8088_0]
                · linarith only [h0, h8051, h8073, hlam]
              · linarith only [h0, h8050, h8072, hlam]
      · linarith only [h0, h7361, h8051, hlam]
    · linarith only [h0, h7360, h8050, hlam]

end R2N4
