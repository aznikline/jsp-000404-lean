import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11652 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11653 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11654 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11655 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11656 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11657 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11658 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h11659 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h12293 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 4 5 (by decide) (by decide) with h12401 | h12401
  · rcases m.htr 3 4 5 (by decide) (by decide) with h12402 | h12402
    · rcases h2bigk with h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c | h12403c
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h0, hlam, p12403_1]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12406 | h12406
        · rcases p12403_3 (m.d 1 2) (by simp) with h12407 | h12407
          · rcases p12403_3 (m.d 2 3) (by simp) with h12408 | h12408
            · linarith only [h12408, hlam, p12403_0]
            · rcases p12403_3 (m.d 2 4) (by simp) with h12410 | h12410
              · linarith only [h11649, h12410, hlam]
              · linarith only [h11659, h12410, hlam]
          · linarith only [h11654, h12407, hlam]
        · linarith only [h12406, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12415 | h12415
        · rcases p12403_3 (m.d 1 2) (by simp) with h12416 | h12416
          · rcases p12403_3 (m.d 2 3) (by simp) with h12417 | h12417
            · linarith only [h11648, h12417, hlam]
            · rcases p12403_3 (m.d 2 4) (by simp) with h12419 | h12419
              · linarith only [h12419, hlam, p12403_0]
              · rcases p12403_3 (m.d 2 5) (by simp) with h12421 | h12421
                · linarith only [h11650, h12421, hlam]
                · rcases h3bigk with h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c | h12423c
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h8410, hlam, p12423_1]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12426 | h12426
                    · rcases p12423_3 (m.d 1 3) (by simp) with h12427 | h12427
                      · rcases p12423_3 (m.d 2 3) (by simp) with h12428 | h12428
                        · linarith only [h11648, h12428, hlam]
                        · rcases p12423_3 (m.d 3 4) (by simp) with h12430 | h12430
                          · linarith only [h11651, h12430, hlam]
                          · linarith only [h11659, h12430, hlam]
                      · linarith only [h11654, h12427, hlam]
                    · linarith only [h11648, h12426, hlam]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12435 | h12435
                    · rcases p12423_3 (m.d 1 3) (by simp) with h12436 | h12436
                      · rcases p12423_3 (m.d 2 3) (by simp) with h12437 | h12437
                        · linarith only [h11648, h12437, hlam]
                        · rcases p12423_3 (m.d 3 4) (by simp) with h12439 | h12439
                          · linarith only [h12439, hlam, p12423_0]
                          · rcases p12423_3 (m.d 3 5) (by simp) with h12441 | h12441
                            · linarith only [h11652, h12441, hlam]
                            · rcases h5bigk with h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c | h12443c
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h10008, hlam, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                rcases p12443_3 (m.d 0 5) (by simp) with h12446 | h12446
                                · rcases p12443_3 (m.d 1 5) (by simp) with h12447 | h12447
                                  · rcases p12443_3 (m.d 2 5) (by simp) with h12448 | h12448
                                    · linarith only [h11650, h12448, hlam]
                                    · rcases p12443_3 (m.d 3 5) (by simp) with h12450 | h12450
                                      · linarith only [h11652, h12450, hlam]
                                      · linarith only [h12293, h12450, hlam]
                                  · linarith only [h11655, h12447, hlam]
                                · linarith only [h11650, h12446, hlam]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h0, h11648, h11651, h11653, h12293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                rcases p12443_3 (m.d 0 5) (by simp) with h12456 | h12456
                                · rcases p12443_3 (m.d 1 5) (by simp) with h12457 | h12457
                                  · rcases p12443_3 (m.d 2 5) (by simp) with h12458 | h12458
                                    · linarith only [h11650, h12458, hlam]
                                    · linarith only [h12401, h12458, hlam]
                                  · linarith only [h11658, h12457, hlam]
                                · linarith only [h11653, h12456, hlam]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11658, hc14, hlam, hphi, ht01, p12443_1, u0ehi4]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                rcases p12443_3 (m.d 0 5) (by simp) with h12465 | h12465
                                · linarith only [h10008, h12465, hlam]
                                · linarith only [h11650, h12465, hlam]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11654, h11656, h11658, h12293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                rcases p12443_3 (m.d 0 5) (by simp) with h12469 | h12469
                                · linarith only [h10008, h12469, hlam]
                                · linarith only [h11653, h12469, hlam]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11650, hlam, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11655, hlam, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h12293, hlam, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h0, h11650, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11652, hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11657, hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h0, h11648, h12402, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12423_1, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h0, h11648, h12402, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12423_1, p12443_1]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11653, hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h11658, hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h12401, hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [h12402, hlam, p12443_0]
                              · have p12443_0 := h12443c.1
                                have p12443_1 := h12443c.2.1
                                have p12443_2 := h12443c.2.2.1
                                have p12443_3 := h12443c.2.2.2
                                linarith only [hlam, p12443_0]
                      · linarith only [h11656, h12436, hlam]
                    · linarith only [h12435, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12489 | h12489
                    · rcases p12423_3 (m.d 1 3) (by simp) with h12490 | h12490
                      · rcases p12423_3 (m.d 2 3) (by simp) with h12491 | h12491
                        · linarith only [h11648, h12491, hlam]
                        · rcases p12423_3 (m.d 3 4) (by simp) with h12493 | h12493
                          · linarith only [h11651, h12493, hlam]
                          · linarith only [h12402, h12493, hlam]
                      · linarith only [h11657, h12490, hlam]
                    · linarith only [h12489, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11654, hc12, hlam, hphi, ht01, p12423_1, u0ehi2]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12500 | h12500
                    · linarith only [h12500, h8410, hlam]
                    · linarith only [h11648, h12500, hlam]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12503 | h12503
                    · linarith only [h12503, h8410, hlam]
                    · linarith only [h11651, h12503, hlam]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12506 | h12506
                    · linarith only [h12506, h8410, hlam]
                    · linarith only [h11652, h12506, hlam]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11648, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11654, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11659, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h12293, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11651, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11656, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12516 | h12516
                    · rcases p12423_3 (m.d 1 3) (by simp) with h12517 | h12517
                      · rcases p12423_3 (m.d 2 3) (by simp) with h12518 | h12518
                        · linarith only [h12518, hlam, p12423_0]
                        · rcases p12423_3 (m.d 3 4) (by simp) with h12520 | h12520
                          · rcases p12423_3 (m.d 3 5) (by simp) with h12521 | h12521
                            · linarith only [h12402, h12521, hlam]
                            · linarith only [h12293, h12521, hlam]
                          · linarith only [h12520, hlam, p12423_0]
                      · linarith only [h11654, h12517, hlam]
                    · linarith only [h11648, h12516, hlam]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11651, h12293, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12423_1]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11652, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h11657, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    rcases p12423_3 (m.d 0 3) (by simp) with h12531 | h12531
                    · rcases p12423_3 (m.d 1 3) (by simp) with h12532 | h12532
                      · rcases p12423_3 (m.d 2 3) (by simp) with h12533 | h12533
                        · linarith only [h12533, hlam, p12423_0]
                        · rcases p12423_3 (m.d 3 4) (by simp) with h12535 | h12535
                          · rcases p12423_3 (m.d 3 5) (by simp) with h12536 | h12536
                            · rcases h5bigk with h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c | h12537c
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h10008, hlam, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                rcases p12537_3 (m.d 0 5) (by simp) with h12540 | h12540
                                · rcases p12537_3 (m.d 1 5) (by simp) with h12541 | h12541
                                  · rcases p12537_3 (m.d 2 5) (by simp) with h12542 | h12542
                                    · linarith only [h11650, h12542, hlam]
                                    · rcases p12537_3 (m.d 3 5) (by simp) with h12544 | h12544
                                      · linarith only [h11652, h12544, hlam]
                                      · linarith only [h12293, h12544, hlam]
                                  · linarith only [h11655, h12541, hlam]
                                · linarith only [h11650, h12540, hlam]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11653, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12423_1, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                rcases p12537_3 (m.d 0 5) (by simp) with h12550 | h12550
                                · rcases p12537_3 (m.d 1 5) (by simp) with h12551 | h12551
                                  · rcases p12537_3 (m.d 2 5) (by simp) with h12552 | h12552
                                    · linarith only [h11650, h12552, hlam]
                                    · linarith only [h12401, h12552, hlam]
                                  · linarith only [h11658, h12551, hlam]
                                · linarith only [h11653, h12550, hlam]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hlam, hphi, ht01, p12537_1, u0ehi4]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                rcases p12537_3 (m.d 0 5) (by simp) with h12559 | h12559
                                · linarith only [h10008, h12559, hlam]
                                · linarith only [h11650, h12559, hlam]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12423_1, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                rcases p12537_3 (m.d 0 5) (by simp) with h12563 | h12563
                                · linarith only [h10008, h12563, hlam]
                                · linarith only [h11653, h12563, hlam]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11650, hlam, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11655, hlam, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h12293, hlam, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h0, h11650, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11652, hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11657, hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11652, h11654, h8410, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11651, h11654, h12402, h8410, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12537_1]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11653, hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h11658, hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h12401, hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [h12402, hlam, p12537_0]
                              · have p12537_0 := h12537c.1
                                have p12537_1 := h12537c.2.1
                                have p12537_2 := h12537c.2.2.1
                                have p12537_3 := h12537c.2.2.2
                                linarith only [hlam, p12537_0]
                            · linarith only [h12536, hlam, p12423_0]
                          · linarith only [h11659, h12535, hlam]
                      · linarith only [h11654, h12532, hlam]
                    · linarith only [h11648, h12531, hlam]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [h12402, hlam, p12423_0]
                  · have p12423_0 := h12423c.1
                    have p12423_1 := h12423c.2.1
                    have p12423_2 := h12423c.2.2.1
                    have p12423_3 := h12423c.2.2.2
                    linarith only [hlam, p12423_0]
          · linarith only [h0, h12416, hlam, p12403_1]
        · linarith only [h12415, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12589 | h12589
        · rcases p12403_3 (m.d 1 2) (by simp) with h12590 | h12590
          · rcases p12403_3 (m.d 2 3) (by simp) with h12591 | h12591
            · linarith only [h11648, h12591, hlam]
            · rcases p12403_3 (m.d 2 4) (by simp) with h12593 | h12593
              · linarith only [h11649, h12593, hlam]
              · linarith only [h12401, h12593, hlam]
          · linarith only [h11655, h12590, hlam]
        · linarith only [h12589, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [hc12, hlam, hphi, ht01, p12403_1, u0ehi1]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12600 | h12600
        · linarith only [h0, h12600, hlam]
        · linarith only [h11648, h12600, hlam]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12603 | h12603
        · linarith only [h0, h12603, hlam]
        · linarith only [h11649, h12603, hlam]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12606 | h12606
        · linarith only [h0, h12606, hlam]
        · linarith only [h11650, h12606, hlam]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h11648, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h11654, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h11659, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h12293, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h11649, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h0, hc24, hlam, hphi, ht01, ht12, p12403_1, u0ehi1]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12616 | h12616
        · rcases p12403_3 (m.d 1 2) (by simp) with h12617 | h12617
          · rcases p12403_3 (m.d 2 3) (by simp) with h12618 | h12618
            · linarith only [h11659, h12618, hlam]
            · rcases p12403_3 (m.d 2 4) (by simp) with h12620 | h12620
              · rcases p12403_3 (m.d 2 5) (by simp) with h12621 | h12621
                · linarith only [h12401, h12621, hlam]
                · linarith only [h12293, h12621, hlam]
              · linarith only [h11659, h12620, hlam]
          · linarith only [h11654, h12617, hlam]
        · linarith only [h11648, h12616, hlam]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12628 | h12628
        · rcases p12403_3 (m.d 1 2) (by simp) with h12629 | h12629
          · rcases p12403_3 (m.d 2 3) (by simp) with h12630 | h12630
            · linarith only [h11659, h12630, hlam]
            · rcases p12403_3 (m.d 2 4) (by simp) with h12632 | h12632
              · rcases p12403_3 (m.d 2 5) (by simp) with h12633 | h12633
                · linarith only [h12401, h12633, hlam]
                · rcases h3bigk with h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c | h12635c
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h8410, hlam, p12635_1]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11651, h11659, h12293, hlam, p12403_1, p12635_2]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h0, h11648, h11659, h12293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12635_1]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    rcases p12635_3 (m.d 0 3) (by simp) with h12640 | h12640
                    · rcases p12635_3 (m.d 1 3) (by simp) with h12641 | h12641
                      · rcases p12635_3 (m.d 2 3) (by simp) with h12642 | h12642
                        · linarith only [h11648, h12642, hlam]
                        · rcases p12635_3 (m.d 3 4) (by simp) with h12644 | h12644
                          · linarith only [h11651, h12644, hlam]
                          · linarith only [h12402, h12644, hlam]
                      · linarith only [h11657, h12641, hlam]
                    · linarith only [h12640, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [hc13, hlam, hphi, ht01, p12635_1, u0ehi2]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11651, h11659, h12293, h8410, hlam, p12403_1, p12635_2]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11659, h12293, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12635_1]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    rcases p12635_3 (m.d 0 3) (by simp) with h12653 | h12653
                    · linarith only [h12653, h8410, hlam]
                    · linarith only [h11652, h12653, hlam]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11648, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11654, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11659, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h12293, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11651, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11656, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    rcases p12635_3 (m.d 0 3) (by simp) with h12663 | h12663
                    · rcases p12635_3 (m.d 1 3) (by simp) with h12664 | h12664
                      · rcases p12635_3 (m.d 2 3) (by simp) with h12665 | h12665
                        · linarith only [h12665, hlam, p12635_0]
                        · rcases p12635_3 (m.d 3 4) (by simp) with h12667 | h12667
                          · rcases p12635_3 (m.d 3 5) (by simp) with h12668 | h12668
                            · linarith only [h12402, h12668, hlam]
                            · linarith only [h12293, h12668, hlam]
                          · linarith only [h12667, hlam, p12635_0]
                      · linarith only [h11654, h12664, hlam]
                    · linarith only [h11648, h12663, hlam]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11651, h12293, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12635_1]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11652, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h11657, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    rcases p12635_3 (m.d 0 3) (by simp) with h12678 | h12678
                    · rcases p12635_3 (m.d 1 3) (by simp) with h12679 | h12679
                      · rcases p12635_3 (m.d 2 3) (by simp) with h12680 | h12680
                        · linarith only [h12680, hlam, p12635_0]
                        · rcases p12635_3 (m.d 3 4) (by simp) with h12682 | h12682
                          · rcases p12635_3 (m.d 3 5) (by simp) with h12683 | h12683
                            · rcases h5bigk with h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c | h12684c
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h10008, hlam, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                rcases p12684_3 (m.d 0 5) (by simp) with h12687 | h12687
                                · rcases p12684_3 (m.d 1 5) (by simp) with h12688 | h12688
                                  · rcases p12684_3 (m.d 2 5) (by simp) with h12689 | h12689
                                    · linarith only [h11650, h12689, hlam]
                                    · rcases p12684_3 (m.d 3 5) (by simp) with h12691 | h12691
                                      · linarith only [h11652, h12691, hlam]
                                      · linarith only [h12293, h12691, hlam]
                                  · linarith only [h11655, h12688, hlam]
                                · linarith only [h11650, h12687, hlam]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11653, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12635_1, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                rcases p12684_3 (m.d 0 5) (by simp) with h12697 | h12697
                                · rcases p12684_3 (m.d 1 5) (by simp) with h12698 | h12698
                                  · rcases p12684_3 (m.d 2 5) (by simp) with h12699 | h12699
                                    · linarith only [h11650, h12699, hlam]
                                    · linarith only [h12401, h12699, hlam]
                                  · linarith only [h11658, h12698, hlam]
                                · linarith only [h11653, h12697, hlam]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hlam, hphi, ht01, p12684_1, u0ehi4]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                rcases p12684_3 (m.d 0 5) (by simp) with h12706 | h12706
                                · linarith only [h10008, h12706, hlam]
                                · linarith only [h11650, h12706, hlam]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12635_1, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                rcases p12684_3 (m.d 0 5) (by simp) with h12710 | h12710
                                · linarith only [h10008, h12710, hlam]
                                · linarith only [h11653, h12710, hlam]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11650, hlam, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11655, hlam, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h12293, hlam, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12403_1, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11652, hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11657, hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11652, h11654, h8410, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11651, h11654, h12402, h8410, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12684_1]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11653, hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h11658, hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h12401, hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [h12402, hlam, p12684_0]
                              · have p12684_0 := h12684c.1
                                have p12684_1 := h12684c.2.1
                                have p12684_2 := h12684c.2.2.1
                                have p12684_3 := h12684c.2.2.2
                                linarith only [hlam, p12684_0]
                            · linarith only [h12683, hlam, p12635_0]
                          · linarith only [h11659, h12682, hlam]
                      · linarith only [h11654, h12679, hlam]
                    · linarith only [h11648, h12678, hlam]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [h12402, hlam, p12635_0]
                  · have p12635_0 := h12635c.1
                    have p12635_1 := h12635c.2.1
                    have p12635_2 := h12635c.2.2.1
                    have p12635_3 := h12635c.2.2.2
                    linarith only [hlam, p12635_0]
              · linarith only [h12401, h12632, hlam]
          · linarith only [h11655, h12629, hlam]
        · linarith only [h11650, h12628, hlam]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h11650, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h11655, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        rcases p12403_3 (m.d 0 2) (by simp) with h12739 | h12739
        · rcases p12403_3 (m.d 1 2) (by simp) with h12740 | h12740
          · rcases p12403_3 (m.d 2 3) (by simp) with h12741 | h12741
            · linarith only [h12293, h12741, hlam]
            · rcases p12403_3 (m.d 2 4) (by simp) with h12743 | h12743
              · rcases p12403_3 (m.d 2 5) (by simp) with h12744 | h12744
                · rcases h3bigk with h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c | h12745c
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h8410, hlam, p12745_1]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11651, h12293, h12402, hlam, p12403_1, p12745_2]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11654, h12293, h12402, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12745_1]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11654, h12293, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12745_1]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11654, hc12, hlam, hphi, ht01, p12745_1, u0ehi2]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11651, h12293, h12402, h8410, hlam, p12403_1, p12745_2]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h12293, h12402, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12745_1]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11654, h12293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12745_1]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11648, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11654, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11659, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h12293, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11651, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11656, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    rcases p12745_3 (m.d 0 3) (by simp) with h12763 | h12763
                    · rcases p12745_3 (m.d 1 3) (by simp) with h12764 | h12764
                      · rcases p12745_3 (m.d 2 3) (by simp) with h12765 | h12765
                        · linarith only [h12765, hlam, p12745_0]
                        · rcases p12745_3 (m.d 3 4) (by simp) with h12767 | h12767
                          · rcases p12745_3 (m.d 3 5) (by simp) with h12768 | h12768
                            · linarith only [h12402, h12768, hlam]
                            · linarith only [h12293, h12768, hlam]
                          · linarith only [h12767, hlam, p12745_0]
                      · linarith only [h11654, h12764, hlam]
                    · linarith only [h11648, h12763, hlam]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11651, h12293, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12403_1, p12745_1]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11652, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h11657, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    rcases p12745_3 (m.d 0 3) (by simp) with h12778 | h12778
                    · rcases p12745_3 (m.d 1 3) (by simp) with h12779 | h12779
                      · rcases p12745_3 (m.d 2 3) (by simp) with h12780 | h12780
                        · linarith only [h12780, hlam, p12745_0]
                        · rcases p12745_3 (m.d 3 4) (by simp) with h12782 | h12782
                          · rcases p12745_3 (m.d 3 5) (by simp) with h12783 | h12783
                            · rcases h5bigk with h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c | h12784c
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h10008, hlam, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12403_1, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h10008, h11654, h11656, h11658, h12293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                rcases p12784_3 (m.d 0 5) (by simp) with h12789 | h12789
                                · rcases p12784_3 (m.d 1 5) (by simp) with h12790 | h12790
                                  · rcases p12784_3 (m.d 2 5) (by simp) with h12791 | h12791
                                    · linarith only [h11650, h12791, hlam]
                                    · linarith only [h12401, h12791, hlam]
                                  · linarith only [h11658, h12790, hlam]
                                · linarith only [h11653, h12789, hlam]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hlam, hphi, ht01, p12784_1, u0ehi4]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11654, h11656, h11658, h12293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12403_1, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                rcases p12784_3 (m.d 0 5) (by simp) with h12800 | h12800
                                · linarith only [h10008, h12800, hlam]
                                · linarith only [h11653, h12800, hlam]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11650, hlam, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11655, hlam, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h12293, hlam, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h0, h11650, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11652, hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11657, hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11652, h11654, h8410, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11651, h11654, h12402, h8410, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12784_1]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11653, hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h11658, hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h12401, hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [h12402, hlam, p12784_0]
                              · have p12784_0 := h12784c.1
                                have p12784_1 := h12784c.2.1
                                have p12784_2 := h12784c.2.2.1
                                have p12784_3 := h12784c.2.2.2
                                linarith only [hlam, p12784_0]
                            · linarith only [h12783, hlam, p12745_0]
                          · linarith only [h11659, h12782, hlam]
                      · linarith only [h11654, h12779, hlam]
                    · linarith only [h11648, h12778, hlam]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [h12402, hlam, p12745_0]
                  · have p12745_0 := h12745c.1
                    have p12745_1 := h12745c.2.1
                    have p12745_2 := h12745c.2.2.1
                    have p12745_3 := h12745c.2.2.2
                    linarith only [hlam, p12745_0]
                · linarith only [h12293, h12744, hlam]
              · linarith only [h11659, h12743, hlam]
          · linarith only [h11654, h12740, hlam]
        · linarith only [h11648, h12739, hlam]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [h12401, hlam, p12403_0]
      · have p12403_0 := h12403c.1
        have p12403_1 := h12403c.2.1
        have p12403_2 := h12403c.2.2.1
        have p12403_3 := h12403c.2.2.2
        linarith only [hlam, p12403_0]
    · linarith only [h11659, h12401, h12402, hlam]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h12831 | h12831
    · rcases h2bigk with h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c | h12832c
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h0, hlam, p12832_1]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11648, h11651, h11659, h12401, h12831, hlam, p12832_2]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11648, h11651, h12401, h12831, hlam, p12832_2]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        rcases p12832_3 (m.d 0 2) (by simp) with h12837 | h12837
        · rcases p12832_3 (m.d 1 2) (by simp) with h12838 | h12838
          · rcases p12832_3 (m.d 2 3) (by simp) with h12839 | h12839
            · linarith only [h11648, h12839, hlam]
            · rcases p12832_3 (m.d 2 4) (by simp) with h12841 | h12841
              · linarith only [h11649, h12841, hlam]
              · rcases p12832_3 (m.d 2 5) (by simp) with h12843 | h12843
                · linarith only [h12843, hlam, p12832_0]
                · rcases h3bigk with h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c | h12845c
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h8410, hlam, p12845_1]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11651, h11659, h12401, h12831, hlam, p12845_2]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11654, h11659, h12401, h12831, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12845_1]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    rcases p12845_3 (m.d 0 3) (by simp) with h12850 | h12850
                    · rcases p12845_3 (m.d 1 3) (by simp) with h12851 | h12851
                      · rcases p12845_3 (m.d 2 3) (by simp) with h12852 | h12852
                        · linarith only [h11648, h12852, hlam]
                        · rcases p12845_3 (m.d 3 4) (by simp) with h12854 | h12854
                          · linarith only [h11651, h12854, hlam]
                          · linarith only [h12831, h12854, hlam]
                      · linarith only [h11657, h12851, hlam]
                    · linarith only [h12850, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11654, hc12, hlam, hphi, ht01, p12845_1, u0ehi2]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11651, h11659, h12401, h12831, h8410, hlam, p12845_2]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11659, h12401, h12831, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12845_1]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    rcases p12845_3 (m.d 0 3) (by simp) with h12863 | h12863
                    · linarith only [h12863, h8410, hlam]
                    · linarith only [h11652, h12863, hlam]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11648, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11654, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11659, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h12293, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11651, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11656, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    rcases p12845_3 (m.d 0 3) (by simp) with h12873 | h12873
                    · rcases p12845_3 (m.d 1 3) (by simp) with h12874 | h12874
                      · rcases p12845_3 (m.d 2 3) (by simp) with h12875 | h12875
                        · linarith only [h12875, hlam, p12845_0]
                        · rcases p12845_3 (m.d 3 4) (by simp) with h12877 | h12877
                          · rcases p12845_3 (m.d 3 5) (by simp) with h12878 | h12878
                            · linarith only [h12831, h12878, hlam]
                            · linarith only [h12293, h12878, hlam]
                          · linarith only [h12877, hlam, p12845_0]
                      · linarith only [h11654, h12874, hlam]
                    · linarith only [h11648, h12873, hlam]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11648, h11651, h11659, h12401, h12831, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12845_1]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11652, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h11657, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    rcases p12845_3 (m.d 0 3) (by simp) with h12888 | h12888
                    · rcases p12845_3 (m.d 1 3) (by simp) with h12889 | h12889
                      · rcases p12845_3 (m.d 2 3) (by simp) with h12890 | h12890
                        · linarith only [h12890, hlam, p12845_0]
                        · rcases p12845_3 (m.d 3 4) (by simp) with h12892 | h12892
                          · rcases p12845_3 (m.d 3 5) (by simp) with h12893 | h12893
                            · rcases h5bigk with h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c | h12894c
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h10008, hlam, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11648, h11651, h11653, hlam, p12832_2, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h0, h11648, h11651, h11653, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12845_1, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h0, h11648, h11651, h11653, h11659, h12401, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hlam, hphi, ht01, p12894_1, u0ehi4]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                rcases p12894_3 (m.d 0 5) (by simp) with h12902 | h12902
                                · linarith only [h10008, h12902, hlam]
                                · linarith only [h11650, h12902, hlam]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12845_1, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11654, h11656, h11658, h11659, h12401, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11650, hlam, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11655, hlam, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h12293, hlam, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h12401, hlam, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11652, hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11657, hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11650, h11652, hlam, p12832_2, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11648, h11651, h11659, h12401, h12831, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11653, hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11658, hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h11653, hc04, hc25, hlam, hphi, ht0b, ht5b, p12894_1]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [h12831, hlam, p12894_0]
                              · have p12894_0 := h12894c.1
                                have p12894_1 := h12894c.2.1
                                have p12894_2 := h12894c.2.2.1
                                have p12894_3 := h12894c.2.2.2
                                linarith only [hlam, p12894_0]
                            · linarith only [h12893, hlam, p12845_0]
                          · linarith only [h11659, h12892, hlam]
                      · linarith only [h11654, h12889, hlam]
                    · linarith only [h11648, h12888, hlam]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [h12831, hlam, p12845_0]
                  · have p12845_0 := h12845c.1
                    have p12845_1 := h12845c.2.1
                    have p12845_2 := h12845c.2.2.1
                    have p12845_3 := h12845c.2.2.2
                    linarith only [hlam, p12845_0]
          · linarith only [h11655, h12838, hlam]
        · linarith only [h12837, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [hc12, hlam, hphi, ht01, p12832_1, u0ehi1]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11651, h11654, h11659, h12401, h12831, h8410, hlam, p12832_2]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11651, h11654, h12401, h12831, h8410, hlam, p12832_2]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        rcases p12832_3 (m.d 0 2) (by simp) with h12934 | h12934
        · linarith only [h0, h12934, hlam]
        · linarith only [h11650, h12934, hlam]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11648, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11654, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11659, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h12293, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11649, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11651, h11654, h12401, h12831, h8410, hlam, p12832_1]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11651, h11654, h12401, h12831, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12832_1]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h12401, hlam, p12832_1]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11650, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11655, hlam, p12832_0]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11651, h11654, h12401, h12831, h8410, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12832_1]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [h11651, h11654, h12401, h12831, h8410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12832_1]
      · have p12832_0 := h12832c.1
        have p12832_1 := h12832c.2.1
        have p12832_2 := h12832c.2.2.1
        have p12832_3 := h12832c.2.2.2
        linarith only [hlam, p12832_0]
    · rcases h2bigk with h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c | h12952c
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h0, hlam, p12952_1]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11648, h11651, h11653, h11659, h12831, hlam, p12952_2]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        rcases p12952_3 (m.d 0 2) (by simp) with h12956 | h12956
        · rcases p12952_3 (m.d 1 2) (by simp) with h12957 | h12957
          · rcases p12952_3 (m.d 2 3) (by simp) with h12958 | h12958
            · linarith only [h11648, h12958, hlam]
            · rcases p12952_3 (m.d 2 4) (by simp) with h12960 | h12960
              · linarith only [h12960, hlam, p12952_0]
              · rcases p12952_3 (m.d 2 5) (by simp) with h12962 | h12962
                · linarith only [h11650, h12962, hlam]
                · linarith only [h12401, h12962, hlam]
          · linarith only [h0, h12957, hc02, hlam, hphi, p12952_1, u0ehi0]
        · linarith only [h12956, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        rcases p12952_3 (m.d 0 2) (by simp) with h12967 | h12967
        · rcases p12952_3 (m.d 1 2) (by simp) with h12968 | h12968
          · rcases p12952_3 (m.d 2 3) (by simp) with h12969 | h12969
            · linarith only [h11648, h12969, hlam]
            · rcases p12952_3 (m.d 2 4) (by simp) with h12971 | h12971
              · linarith only [h11649, h12971, hlam]
              · rcases p12952_3 (m.d 2 5) (by simp) with h12973 | h12973
                · linarith only [h12973, hlam, p12952_0]
                · rcases h3bigk with h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c | h12975c
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h8410, hlam, p12975_1]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11651, h11653, h11659, h12831, hlam, p12975_2]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    rcases p12975_3 (m.d 0 3) (by simp) with h12979 | h12979
                    · rcases p12975_3 (m.d 1 3) (by simp) with h12980 | h12980
                      · rcases p12975_3 (m.d 2 3) (by simp) with h12981 | h12981
                        · linarith only [h11648, h12981, hlam]
                        · rcases p12975_3 (m.d 3 4) (by simp) with h12983 | h12983
                          · linarith only [h12983, hlam, p12975_0]
                          · rcases p12975_3 (m.d 3 5) (by simp) with h12985 | h12985
                            · linarith only [h11652, h12985, hlam]
                            · linarith only [h12831, h12985, hlam]
                      · linarith only [h11656, h12980, hlam]
                    · linarith only [h12979, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    rcases p12975_3 (m.d 0 3) (by simp) with h12990 | h12990
                    · rcases p12975_3 (m.d 1 3) (by simp) with h12991 | h12991
                      · rcases p12975_3 (m.d 2 3) (by simp) with h12992 | h12992
                        · linarith only [h11648, h12992, hlam]
                        · rcases p12975_3 (m.d 3 4) (by simp) with h12994 | h12994
                          · linarith only [h11651, h12994, hlam]
                          · rcases p12975_3 (m.d 3 5) (by simp) with h12996 | h12996
                            · linarith only [h12996, hlam, p12975_0]
                            · rcases h5bigk with h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c | h12998c
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h10008, hlam, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11650, hlam, p12952_2, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11652, hlam, p12975_2, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h10008, h11654, h11656, h11658, h11659, h12831, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11654, h11656, h11658, hc12, hlam, hphi, ht01, p12998_1, u0ehi4]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                rcases p12998_3 (m.d 0 5) (by simp) with h13006 | h13006
                                · linarith only [h10008, h13006, hlam]
                                · linarith only [h11650, h13006, hlam]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11654, h11656, h11658, h11659, h12831, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11654, h11656, h11658, h11659, h12831, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11650, hlam, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11655, hlam, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h12293, hlam, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h12401, hlam, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11652, hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11657, hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11648, h11651, h11653, h11659, h12831, hc23, hc35, hlam, hphi, p12952_2, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h12831, hlam, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11653, hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11658, hlam, p12998_0]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11648, h11651, h11653, hlam, p12952_2, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [h11648, h11651, h11653, hc02, hc35, hlam, hphi, ht0b, ht5b, p12998_1]
                              · have p12998_0 := h12998c.1
                                have p12998_1 := h12998c.2.1
                                have p12998_2 := h12998c.2.2.1
                                have p12998_3 := h12998c.2.2.2
                                linarith only [hlam, p12998_0]
                      · linarith only [h11657, h12991, hlam]
                    · linarith only [h12990, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11651, h11653, h11654, h11659, h12831, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12975_1]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11651, h11653, h11659, h12831, h8410, hlam, p12975_2]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    rcases p12975_3 (m.d 0 3) (by simp) with h13031 | h13031
                    · linarith only [h13031, h8410, hlam]
                    · linarith only [h11651, h13031, hlam]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    rcases p12975_3 (m.d 0 3) (by simp) with h13034 | h13034
                    · linarith only [h13034, h8410, hlam]
                    · linarith only [h11652, h13034, hlam]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11648, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11654, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11659, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h12293, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11651, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11656, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11648, h11651, h11653, h12831, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12975_1]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h12831, hlam, p12975_1]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11652, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11657, hlam, p12975_0]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    rcases p12975_3 (m.d 0 3) (by simp) with h13049 | h13049
                    · rcases p12975_3 (m.d 1 3) (by simp) with h13050 | h13050
                      · rcases p12975_3 (m.d 2 3) (by simp) with h13051 | h13051
                        · linarith only [h13051, hlam, p12975_0]
                        · rcases p12975_3 (m.d 3 4) (by simp) with h13053 | h13053
                          · linarith only [h12831, h13053, hlam]
                          · linarith only [h11659, h13053, hlam]
                      · linarith only [h11654, h13050, hlam]
                    · linarith only [h11648, h13049, hlam]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [h11659, hc23, hc35, hlam, hphi, p12975_1]
                  · have p12975_0 := h12975c.1
                    have p12975_1 := h12975c.2.1
                    have p12975_2 := h12975c.2.2.1
                    have p12975_3 := h12975c.2.2.2
                    linarith only [hlam, p12975_0]
          · linarith only [h11655, h12968, hlam]
        · linarith only [h12967, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [hc12, hlam, hphi, ht01, p12952_1, u0ehi1]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h0, h11648, h11651, h11653, h11659, h12831, hlam, p12952_2]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        rcases p12952_3 (m.d 0 2) (by simp) with h13065 | h13065
        · linarith only [h0, h13065, hlam]
        · linarith only [h11649, h13065, hlam]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        rcases p12952_3 (m.d 0 2) (by simp) with h13068 | h13068
        · linarith only [h0, h13068, hlam]
        · linarith only [h11650, h13068, hlam]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11648, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11654, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11659, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h12293, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11649, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h0, h11648, h11651, h11653, h11659, h12831, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12952_1]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11648, h11651, h11653, h11659, h12831, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12952_1]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h12401, hlam, p12952_1]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11650, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [h11655, hlam, p12952_0]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        rcases p12952_3 (m.d 0 2) (by simp) with h13083 | h13083
        · rcases p12952_3 (m.d 1 2) (by simp) with h13084 | h13084
          · rcases p12952_3 (m.d 2 3) (by simp) with h13085 | h13085
            · linarith only [h12293, h13085, hlam]
            · rcases p12952_3 (m.d 2 4) (by simp) with h13087 | h13087
              · linarith only [h12401, h13087, hlam]
              · linarith only [h11659, h13087, hlam]
          · linarith only [h11654, h13084, hlam]
        · linarith only [h11648, h13083, hlam]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        rcases p12952_3 (m.d 0 2) (by simp) with h13092 | h13092
        · rcases p12952_3 (m.d 1 2) (by simp) with h13093 | h13093
          · rcases p12952_3 (m.d 2 3) (by simp) with h13094 | h13094
            · linarith only [h12293, h13094, hlam]
            · rcases p12952_3 (m.d 2 4) (by simp) with h13096 | h13096
              · linarith only [h12401, h13096, hlam]
              · rcases p12952_3 (m.d 2 5) (by simp) with h13098 | h13098
                · rcases h3bigk with h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c | h13099c
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h8410, hlam, p13099_1]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11651, h11653, h11659, h12831, hlam, p13099_2]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    rcases p13099_3 (m.d 0 3) (by simp) with h13103 | h13103
                    · rcases p13099_3 (m.d 1 3) (by simp) with h13104 | h13104
                      · rcases p13099_3 (m.d 2 3) (by simp) with h13105 | h13105
                        · linarith only [h11648, h13105, hlam]
                        · rcases p13099_3 (m.d 3 4) (by simp) with h13107 | h13107
                          · linarith only [h13107, hlam, p13099_0]
                          · rcases p13099_3 (m.d 3 5) (by simp) with h13109 | h13109
                            · linarith only [h11652, h13109, hlam]
                            · linarith only [h12831, h13109, hlam]
                      · linarith only [h11656, h13104, hlam]
                    · linarith only [h13103, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h0, h11648, h11659, h12293, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12952_1, p13099_1]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11651, h11653, h11654, h12831, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13099_1]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11652, h11659, h12293, h8410, hlam, p12952_1, p13099_2]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    rcases p13099_3 (m.d 0 3) (by simp) with h13118 | h13118
                    · linarith only [h13118, h8410, hlam]
                    · linarith only [h11651, h13118, hlam]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11659, h12293, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12952_1, p13099_1]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11648, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11654, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11659, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h12293, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11651, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11656, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11651, h11653, h12831, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13099_1]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h12831, hlam, p13099_1]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11652, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11657, hlam, p13099_0]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    rcases p13099_3 (m.d 0 3) (by simp) with h13134 | h13134
                    · rcases p13099_3 (m.d 1 3) (by simp) with h13135 | h13135
                      · rcases p13099_3 (m.d 2 3) (by simp) with h13136 | h13136
                        · linarith only [h13136, hlam, p13099_0]
                        · rcases p13099_3 (m.d 3 4) (by simp) with h13138 | h13138
                          · linarith only [h12831, h13138, hlam]
                          · linarith only [h11659, h13138, hlam]
                      · linarith only [h11654, h13135, hlam]
                    · linarith only [h11648, h13134, hlam]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [h11659, hc23, hc35, hlam, hphi, p13099_1]
                  · have p13099_0 := h13099c.1
                    have p13099_1 := h13099c.2.1
                    have p13099_2 := h13099c.2.2.1
                    have p13099_3 := h13099c.2.2.2
                    linarith only [hlam, p13099_0]
                · linarith only [h12401, h13098, hlam]
          · linarith only [h0, h13093, hc25, hlam, hphi, ht01, ht12, p12952_1, u0ehi1]
        · linarith only [h11649, h13092, hlam]
      · have p12952_0 := h12952c.1
        have p12952_1 := h12952c.2.1
        have p12952_2 := h12952c.2.2.1
        have p12952_3 := h12952c.2.2.2
        linarith only [hlam, p12952_0]

set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11648 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11649 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11650 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11651 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11652 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11653 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h11654 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11655 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h11656 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11657 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h11658 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h11659 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 3 5 (by decide) (by decide) with h12293 | h12293
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651 h11652 h11653 h11654 h11655 h11656 h11657 h11658 h11659 h12293
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg8410 h10008 h11648 h11649 h11650 h11651 h11652 h11653 h11654 h11655 h11656 h11657 h11658 h11659 h12293

end R2N4
