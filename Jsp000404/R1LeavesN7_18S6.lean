import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2947 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3245 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3470 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h3471 | h3471
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3472 | h3472
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3473 | h3473
      · linarith only [h0, h3473, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3475 | h3475
        · linarith only [h0, h2947, h3475, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3477 | h3477
          · linarith only [h0, h3245, h3477, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3479 | h3479
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3480 | h3480
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3481 | h3481
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3482 | h3482
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3483 | h3483
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3484 | h3484
                      · rcases h0bigk with h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c | h3485c
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          rcases p3485_3 (m.d 0 1) (by simp) with h3487 | h3487
                          · rcases p3485_3 (m.d 0 2) (by simp) with h3488 | h3488
                            · linarith only [h0, h3488, hlam]
                            · rcases p3485_3 (m.d 0 3) (by simp) with h3490 | h3490
                              · linarith only [h1, h3490, hlam]
                              · linarith only [h3490, h4, hlam]
                          · linarith only [h0, h3487, hlam]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h1, h3479, h3484, hc01, hc45, hlam, hphi, ht0b, ht5b, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h2, h3479, h3484, hc01, hc45, hlam, hphi, ht0b, ht5b, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          rcases p3485_3 (m.d 0 1) (by simp) with h3496 | h3496
                          · rcases p3485_3 (m.d 0 2) (by simp) with h3497 | h3497
                            · linarith only [h0, h3497, hlam]
                            · rcases p3485_3 (m.d 0 3) (by simp) with h3499 | h3499
                              · linarith only [h1, h3499, hlam]
                              · linarith only [h3471, h3499, hlam]
                          · linarith only [h3, h3496, hlam]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h0, hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h4, hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h2947, hlam, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h3245, hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h1, hlam, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h2, h3479, h3484, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h0, h3245, h4, hc12, hc23, hlam, hphi, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h2, hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h3470, hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h0, h3245, h3470, h4, hc12, hc23, hlam, hphi, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h3, hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h3471, hlam, p3485_0]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [h3472, hlam, p3485_1]
                        · have p3485_0 := h3485c.1
                          have p3485_1 := h3485c.2.1
                          have p3485_2 := h3485c.2.2.1
                          have p3485_3 := h3485c.2.2.2
                          linarith only [hlam, p3485_0]
                      · rcases h0bigk with h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          rcases p3523_3 (m.d 0 1) (by simp) with h3525 | h3525
                          · rcases p3523_3 (m.d 0 2) (by simp) with h3526 | h3526
                            · linarith only [h0, h3526, hlam]
                            · rcases p3523_3 (m.d 0 3) (by simp) with h3528 | h3528
                              · linarith only [h1, h3528, hlam]
                              · linarith only [h3528, h4, hlam]
                          · linarith only [h0, h3525, hlam]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h1, h3480, h3484, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3472, h3484, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3472, h3484, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h0, hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h4, hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h2947, hlam, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3245, hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h1, hlam, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3472, h3484, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h0, h3245, h4, hc12, hc23, hlam, hphi, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h2, hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h0, h2947, h3481, hc12, hc23, hlam, hphi, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3470, hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h0, h2947, h3245, h3481, hc12, hc23, hlam, hphi, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3, hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h0, h3245, h3481, h3483, hc12, hc23, hlam, hphi, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3471, hlam, p3523_0]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [h3472, hlam, p3523_1]
                        · have p3523_0 := h3523c.1
                          have p3523_1 := h3523c.2.1
                          have p3523_2 := h3523c.2.2.1
                          have p3523_3 := h3523c.2.2.2
                          linarith only [hlam, p3523_0]
                    · linarith only [h2947, h3472, h3483, hlam]
                  · linarith only [h1, h3480, h3482, h4, hlam]
                · linarith only [h3470, h3481, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3558 | h3558
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3559 | h3559
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3560 | h3560
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3561 | h3561
                      · linarith only [h3471, h3479, h3480, h3561, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases h0bigk with h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          rcases p3563_3 (m.d 0 1) (by simp) with h3565 | h3565
                          · rcases p3563_3 (m.d 0 2) (by simp) with h3566 | h3566
                            · linarith only [h0, h3566, hlam]
                            · rcases p3563_3 (m.d 0 3) (by simp) with h3568 | h3568
                              · linarith only [h1, h3568, hlam]
                              · linarith only [h3568, h4, hlam]
                          · linarith only [h0, h3565, hlam]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3470, h3472, h3480, h3561, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3472, h3480, h3561, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3471, h3480, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h0, hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h4, hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h2947, hlam, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3245, hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h1, hlam, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3472, h3480, h3561, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h0, h3245, h4, hc12, hc23, hlam, hphi, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h2, hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h0, h2947, h3558, hc12, hc23, hlam, hphi, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3470, hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h2947, h3471, h3480, h3558, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3, hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h0, h3245, h3558, h3560, hc12, hc23, hlam, hphi, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3471, hlam, p3563_0]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [h3472, hlam, p3563_1]
                        · have p3563_0 := h3563c.1
                          have p3563_1 := h3563c.2.1
                          have p3563_2 := h3563c.2.2.1
                          have p3563_3 := h3563c.2.2.2
                          linarith only [hlam, p3563_0]
                    · linarith only [h2947, h3471, h3472, h3479, h3480, h3560, hc34, hc45, hlam, hphi]
                  · linarith only [h3471, h3559, h4, hlam]
                · linarith only [h3479, h3480, h3558, h4, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3598 | h3598
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3599 | h3599
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3600 | h3600
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3601 | h3601
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3602 | h3602
                      · rcases h0bigk with h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c | h3603c
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          rcases p3603_3 (m.d 0 1) (by simp) with h3605 | h3605
                          · rcases p3603_3 (m.d 0 2) (by simp) with h3606 | h3606
                            · linarith only [h0, h3606, hlam]
                            · rcases p3603_3 (m.d 0 3) (by simp) with h3608 | h3608
                              · linarith only [h1, h3608, hlam]
                              · linarith only [h3608, h4, hlam]
                          · linarith only [h0, h3605, hlam]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h3470, h3479, h3598, h3602, hc01, hc45, hlam, hphi, ht0b, ht5b, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h2, h3479, h3598, h3602, hc01, hc45, hlam, hphi, ht0b, ht5b, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          rcases p3603_3 (m.d 0 1) (by simp) with h3614 | h3614
                          · rcases p3603_3 (m.d 0 2) (by simp) with h3615 | h3615
                            · linarith only [h0, h3615, hlam]
                            · rcases p3603_3 (m.d 0 3) (by simp) with h3617 | h3617
                              · linarith only [h1, h3617, hlam]
                              · linarith only [h3471, h3617, hlam]
                          · linarith only [h3, h3614, hlam]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h0, hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h4, hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h2947, hlam, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h3245, hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h1, hlam, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h3470, h3479, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h0, h3245, h4, hc12, hc23, hlam, hphi, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h2, hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h0, h2947, h3599, hc12, hc23, hlam, hphi, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h3470, hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h0, h2947, h3245, h3599, hc12, hc23, hlam, hphi, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h3, hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h0, h3245, h3599, h3601, hc12, hc23, hlam, hphi, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h3471, hlam, p3603_0]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [h3472, hlam, p3603_1]
                        · have p3603_0 := h3603c.1
                          have p3603_1 := h3603c.2.1
                          have p3603_2 := h3603c.2.2.1
                          have p3603_3 := h3603c.2.2.2
                          linarith only [hlam, p3603_0]
                      · linarith only [h2947, h3472, h3479, h3598, h3599, h3602, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h2947, h3472, h3601, hlam]
                  · linarith only [h3479, h3598, h3600, hc23, hc34, hlam, hphi]
                · linarith only [h3470, h3599, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3645 | h3645
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3646 | h3646
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3647 | h3647
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3648 | h3648
                      · rcases h0bigk with h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c | h3649c
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          rcases p3649_3 (m.d 0 1) (by simp) with h3651 | h3651
                          · rcases p3649_3 (m.d 0 2) (by simp) with h3652 | h3652
                            · linarith only [h0, h3652, hlam]
                            · rcases p3649_3 (m.d 0 3) (by simp) with h3654 | h3654
                              · linarith only [h1, h3654, hlam]
                              · linarith only [h3654, h4, hlam]
                          · linarith only [h0, h3651, hlam]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3470, h3598, h3648, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3470, h3598, h3648, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3471, h3598, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h0, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h4, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2947, hlam, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3245, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h1, hlam, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3470, h3598, h3648, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3471, h3598, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h2, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3470, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3470, h3471, h3598, h4, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3471, hlam, p3649_0]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [h3472, hlam, p3649_1]
                        · have p3649_0 := h3649c.1
                          have p3649_1 := h3649c.2.1
                          have p3649_2 := h3649c.2.2.1
                          have p3649_3 := h3649c.2.2.2
                          linarith only [hlam, p3649_0]
                      · linarith only [h3470, h3472, h3473, h3479, h3648, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h2947, h3470, h3472, h3647, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h3470, h3473, h3479, h3646, h4, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h3470, h3645, h4, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3685 | h3685
      · linarith only [h0, h3685, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3687 | h3687
        · linarith only [h0, h2947, h3687, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3689 | h3689
          · linarith only [h0, h3245, h3689, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3691 | h3691
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3692 | h3692
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3693 | h3693
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3694 | h3694
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3695 | h3695
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3696 | h3696
                      · linarith only [h1, h2, h3472, h3687, h3691, h3696, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h0bigk with h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          rcases p3698_3 (m.d 0 1) (by simp) with h3700 | h3700
                          · rcases p3698_3 (m.d 0 2) (by simp) with h3701 | h3701
                            · linarith only [h0, h3701, hlam]
                            · rcases p3698_3 (m.d 0 3) (by simp) with h3703 | h3703
                              · linarith only [h1, h3703, hlam]
                              · linarith only [h3703, h4, hlam]
                          · linarith only [h0, h3700, hlam]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h3470, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          rcases p3698_3 (m.d 0 1) (by simp) with h3708 | h3708
                          · rcases p3698_3 (m.d 0 2) (by simp) with h3709 | h3709
                            · linarith only [h0, h3709, hlam]
                            · rcases p3698_3 (m.d 0 3) (by simp) with h3711 | h3711
                              · linarith only [h1, h3711, hlam]
                              · linarith only [h3470, h3711, hlam]
                          · linarith only [h2, h3708, hlam]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          rcases p3698_3 (m.d 0 1) (by simp) with h3715 | h3715
                          · rcases p3698_3 (m.d 0 2) (by simp) with h3716 | h3716
                            · linarith only [h0, h3716, hlam]
                            · rcases p3698_3 (m.d 0 3) (by simp) with h3718 | h3718
                              · linarith only [h1, h3718, hlam]
                              · linarith only [h3471, h3718, hlam]
                          · linarith only [h3, h3715, hlam]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h0, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h4, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h2947, hlam, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h3245, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h1, hlam, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h4, hc02, hc23, hlam, hphi, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h2, h3687, h4, hc12, hc23, hlam, hphi, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h0, h3245, h4, hc12, hc23, hlam, hphi, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h2, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h0, h3472, h3695, hc12, hc24, hlam, hphi, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h3470, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h3472, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h3, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h3471, hlam, p3698_0]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [h3472, h3695, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3698_1]
                        · have p3698_0 := h3698c.1
                          have p3698_1 := h3698c.2.1
                          have p3698_2 := h3698c.2.2.1
                          have p3698_3 := h3698c.2.2.2
                          linarith only [hlam, p3698_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3742 | h3742
                      · linarith only [h0, h2947, h3695, h3742, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c | h3744c
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          rcases p3744_3 (m.d 0 1) (by simp) with h3746 | h3746
                          · rcases p3744_3 (m.d 0 2) (by simp) with h3747 | h3747
                            · linarith only [h0, h3747, hlam]
                            · rcases p3744_3 (m.d 0 3) (by simp) with h3749 | h3749
                              · linarith only [h1, h3749, hlam]
                              · linarith only [h3749, h4, hlam]
                          · linarith only [h0, h3746, hlam]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h3470, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          rcases p3744_3 (m.d 0 1) (by simp) with h3754 | h3754
                          · rcases p3744_3 (m.d 0 2) (by simp) with h3755 | h3755
                            · linarith only [h0, h3755, hlam]
                            · rcases p3744_3 (m.d 0 3) (by simp) with h3757 | h3757
                              · linarith only [h1, h3757, hlam]
                              · linarith only [h3470, h3757, hlam]
                          · linarith only [h2, h3754, hlam]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          rcases p3744_3 (m.d 0 1) (by simp) with h3761 | h3761
                          · rcases p3744_3 (m.d 0 2) (by simp) with h3762 | h3762
                            · linarith only [h0, h3762, hlam]
                            · rcases p3744_3 (m.d 0 3) (by simp) with h3764 | h3764
                              · linarith only [h1, h3764, hlam]
                              · linarith only [h3471, h3764, hlam]
                          · linarith only [h3, h3761, hlam]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h0, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h4, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h2947, hlam, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h3245, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h1, hlam, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h4, hc02, hc23, hlam, hphi, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h2, h3687, h4, hc12, hc23, hlam, hphi, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h2, h3472, h3687, h4, hc12, hc23, hlam, hphi, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h2, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h3470, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h3472, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h3, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h3471, hlam, p3744_0]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [h3472, hc04, hc45, hlam, hphi, p3744_1]
                        · have p3744_0 := h3744c.1
                          have p3744_1 := h3744c.2.1
                          have p3744_2 := h3744c.2.2.1
                          have p3744_3 := h3744c.2.2.2
                          linarith only [hlam, p3744_0]
                  · linarith only [h1, h3692, h3694, h4, hlam]
                · linarith only [h3470, h3693, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3790 | h3790
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3791 | h3791
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3792 | h3792
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3793 | h3793
                      · linarith only [h3471, h3472, h3691, h3692, h3793, hlam]
                      · rcases h0bigk with h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c | h3795c
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          rcases p3795_3 (m.d 0 1) (by simp) with h3797 | h3797
                          · rcases p3795_3 (m.d 0 2) (by simp) with h3798 | h3798
                            · linarith only [h0, h3798, hlam]
                            · rcases p3795_3 (m.d 0 3) (by simp) with h3800 | h3800
                              · linarith only [h1, h3800, hlam]
                              · linarith only [h3800, h4, hlam]
                          · linarith only [h0, h3797, hlam]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h1, h3691, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          rcases p3795_3 (m.d 0 1) (by simp) with h3805 | h3805
                          · rcases p3795_3 (m.d 0 2) (by simp) with h3806 | h3806
                            · linarith only [h0, h3806, hlam]
                            · rcases p3795_3 (m.d 0 3) (by simp) with h3808 | h3808
                              · linarith only [h1, h3808, hlam]
                              · linarith only [h3470, h3808, hlam]
                          · linarith only [h2, h3805, hlam]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3471, h3691, h3692, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h4, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h2947, hlam, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3245, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h1, hlam, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h2947, h4, hc12, hc23, hlam, hphi, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h3245, h4, hc12, hc23, hlam, hphi, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h2, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h2947, h3790, hc12, hc23, hlam, hphi, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3470, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3472, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h0, h3245, h3790, h3792, hc12, hc23, hlam, hphi, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3471, hlam, p3795_0]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [h3472, h3790, h3792, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3795_1]
                        · have p3795_0 := h3795c.1
                          have p3795_1 := h3795c.2.1
                          have p3795_2 := h3795c.2.2.1
                          have p3795_3 := h3795c.2.2.2
                          linarith only [hlam, p3795_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3833 | h3833
                      · linarith only [h3245, h3471, h3691, h3692, h3792, h3833, h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases h0bigk with h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c | h3835c
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          rcases p3835_3 (m.d 0 1) (by simp) with h3837 | h3837
                          · rcases p3835_3 (m.d 0 2) (by simp) with h3838 | h3838
                            · linarith only [h0, h3838, hlam]
                            · rcases p3835_3 (m.d 0 3) (by simp) with h3840 | h3840
                              · linarith only [h1, h3840, hlam]
                              · linarith only [h3840, h4, hlam]
                          · linarith only [h0, h3837, hlam]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3471, h3692, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          rcases p3835_3 (m.d 0 1) (by simp) with h3845 | h3845
                          · rcases p3835_3 (m.d 0 2) (by simp) with h3846 | h3846
                            · linarith only [h0, h3846, hlam]
                            · rcases p3835_3 (m.d 0 3) (by simp) with h3848 | h3848
                              · linarith only [h1, h3848, hlam]
                              · linarith only [h3470, h3848, hlam]
                          · linarith only [h2, h3845, hlam]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3471, h3691, h3692, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h0, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h4, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h2947, hlam, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3245, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h1, hlam, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h2, h3687, h4, hc12, hc23, hlam, hphi, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3471, h3691, h3692, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h2, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3470, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3472, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3471, hlam, p3835_0]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [h3472, hc04, hc45, hlam, hphi, p3835_1]
                        · have p3835_0 := h3835c.1
                          have p3835_1 := h3835c.2.1
                          have p3835_2 := h3835c.2.2.1
                          have p3835_3 := h3835c.2.2.2
                          linarith only [hlam, p3835_0]
                  · linarith only [h3471, h3791, h4, hlam]
                · linarith only [h3471, h3691, h3692, h3790, h4, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3875 | h3875
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3876 | h3876
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3877 | h3877
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3878 | h3878
                    · linarith only [h3470, h3472, h3691, h3875, h3878, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3880 | h3880
                      · linarith only [h2947, h3470, h3878, h3880, hlam]
                      · linarith only [h3691, h3875, h3880, hlam]
                  · linarith only [h3470, h3691, h3875, h3877, h4, hlam]
                · linarith only [h3470, h3876, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3885 | h3885
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3886 | h3886
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3887 | h3887
                    · linarith only [h3470, h3472, h3685, h3691, h3887, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3889 | h3889
                      · linarith only [h2947, h3470, h3887, h3889, hlam]
                      · rcases h0bigk with h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c | h3891c
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          rcases p3891_3 (m.d 0 1) (by simp) with h3893 | h3893
                          · rcases p3891_3 (m.d 0 2) (by simp) with h3894 | h3894
                            · linarith only [h0, h3894, hlam]
                            · rcases p3891_3 (m.d 0 3) (by simp) with h3896 | h3896
                              · linarith only [h1, h3896, hlam]
                              · linarith only [h3896, h4, hlam]
                          · linarith only [h0, h3893, hlam]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3470, h3685, h3691, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3470, h3685, h3691, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3471, h3685, h3691, h3889, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h0, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h4, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2947, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3245, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h1, hlam, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3470, h3685, h3691, h4, hc12, hc23, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h0, h3245, h4, hc12, hc23, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h2, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3470, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3472, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3471, hlam, p3891_0]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [h3472, hc04, hc45, hlam, hphi, p3891_1]
                        · have p3891_0 := h3891c.1
                          have p3891_1 := h3891c.2.1
                          have p3891_2 := h3891c.2.2.1
                          have p3891_3 := h3891c.2.2.2
                          linarith only [hlam, p3891_0]
                  · linarith only [h3471, h3886, h4, hlam]
                · linarith only [h3470, h3885, h4, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3925 | h3925
    · linarith only [h3470, h3471, h3925, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3927 | h3927
      · linarith only [h0, h3927, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3929 | h3929
        · linarith only [h0, h2947, h3929, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3931 | h3931
          · linarith only [h0, h3245, h3931, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3933 | h3933
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3934 | h3934
              · linarith only [h1, h3471, h3934, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3936 | h3936
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3937 | h3937
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3938 | h3938
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3939 | h3939
                      · linarith only [h0, h2947, h3470, h3471, h3925, h3937, h3939, hc12, hc23, hlam, hphi]
                      · rcases h0bigk with h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c | h3941c
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          rcases p3941_3 (m.d 0 1) (by simp) with h3943 | h3943
                          · rcases p3941_3 (m.d 0 2) (by simp) with h3944 | h3944
                            · linarith only [h0, h3944, hlam]
                            · rcases p3941_3 (m.d 0 3) (by simp) with h3946 | h3946
                              · linarith only [h1, h3946, hlam]
                              · linarith only [h3946, h4, hlam]
                          · linarith only [h0, h3943, hlam]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h1, h3933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          rcases p3941_3 (m.d 0 1) (by simp) with h3951 | h3951
                          · rcases p3941_3 (m.d 0 2) (by simp) with h3952 | h3952
                            · linarith only [h0, h3952, hlam]
                            · rcases p3941_3 (m.d 0 3) (by simp) with h3954 | h3954
                              · linarith only [h1, h3954, hlam]
                              · linarith only [h3470, h3954, hlam]
                          · linarith only [h2, h3951, hlam]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h1, h3471, h3933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h0, hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h4, hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h2947, hlam, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h3245, hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h1, hlam, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h0, h3471, h3936, h3938, h3939, hc12, hc23, hlam, hphi, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h0, h2947, h3471, h3936, h3938, h3939, hc12, hc23, hlam, hphi, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h3471, hlam, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h2, hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h0, h2947, h3936, hc12, hc23, hlam, hphi, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h3470, hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h3925, hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h3, hlam, p3941_0]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h1, h3471, h3933, h3936, h3938, h3939, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [h3471, h3936, h3938, h3939, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3941_1]
                        · have p3941_0 := h3941c.1
                          have p3941_1 := h3941c.2.1
                          have p3941_2 := h3941c.2.2.1
                          have p3941_3 := h3941c.2.2.2
                          linarith only [hlam, p3941_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3979 | h3979
                      · linarith only [h1, h3933, h3938, h3979, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c | h3981c
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          rcases p3981_3 (m.d 0 1) (by simp) with h3983 | h3983
                          · rcases p3981_3 (m.d 0 2) (by simp) with h3984 | h3984
                            · linarith only [h0, h3984, hlam]
                            · rcases p3981_3 (m.d 0 3) (by simp) with h3986 | h3986
                              · linarith only [h1, h3986, hlam]
                              · linarith only [h3986, h4, hlam]
                          · linarith only [h0, h3983, hlam]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h1, h3933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          rcases p3981_3 (m.d 0 1) (by simp) with h3991 | h3991
                          · rcases p3981_3 (m.d 0 2) (by simp) with h3992 | h3992
                            · linarith only [h0, h3992, hlam]
                            · rcases p3981_3 (m.d 0 3) (by simp) with h3994 | h3994
                              · linarith only [h1, h3994, hlam]
                              · linarith only [h3470, h3994, hlam]
                          · linarith only [h2, h3991, hlam]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h1, h3471, h3933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h0, hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h4, hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h2947, hlam, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h3245, hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h1, hlam, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h0, h2947, h4, hc12, hc23, hlam, hphi, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h3471, hlam, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h2, hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h3470, hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h3925, hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h3, hlam, p3981_0]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h3471, h3937, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [h3471, h3937, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3981_1]
                        · have p3981_0 := h3981c.1
                          have p3981_1 := h3981c.2.1
                          have p3981_2 := h3981c.2.2.1
                          have p3981_3 := h3981c.2.2.2
                          linarith only [hlam, p3981_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4019 | h4019
                    · linarith only [h2, h3925, h3929, h3936, h3937, h4019, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4021 | h4021
                      · linarith only [h1, h3933, h4019, h4021, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          rcases p4023_3 (m.d 0 1) (by simp) with h4025 | h4025
                          · rcases p4023_3 (m.d 0 2) (by simp) with h4026 | h4026
                            · linarith only [h0, h4026, hlam]
                            · rcases p4023_3 (m.d 0 3) (by simp) with h4028 | h4028
                              · linarith only [h1, h4028, hlam]
                              · linarith only [h4, h4028, hlam]
                          · linarith only [h0, h4025, hlam]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h1, h3933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          rcases p4023_3 (m.d 0 1) (by simp) with h4033 | h4033
                          · rcases p4023_3 (m.d 0 2) (by simp) with h4034 | h4034
                            · linarith only [h0, h4034, hlam]
                            · rcases p4023_3 (m.d 0 3) (by simp) with h4036 | h4036
                              · linarith only [h1, h4036, hlam]
                              · linarith only [h3470, h4036, hlam]
                          · linarith only [h2, h4033, hlam]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h1, h3471, h3933, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h0, hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h4, hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h2947, hlam, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h3245, hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h1, hlam, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h0, h3471, hc12, hc35, hlam, hphi, ht23, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h0, h2947, h3471, h4021, hc12, hc45, hlam, hphi, ht23, ht34, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h3471, hlam, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h2, hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h3470, hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h3925, hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h3, hlam, p4023_0]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h3471, h4021, hc03, hc45, hlam, hphi, ht34, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [h3471, h4021, hc04, hc45, hlam, hphi, p4023_1]
                        · have p4023_0 := h4023c.1
                          have p4023_1 := h4023c.2.1
                          have p4023_2 := h4023c.2.2.1
                          have p4023_3 := h4023c.2.2.2
                          linarith only [hlam, p4023_0]
                · linarith only [h0, h1, h3933, h3936, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h3470, h3471, h3933, hc13, hc35, hlam, hphi]

end R2N4
