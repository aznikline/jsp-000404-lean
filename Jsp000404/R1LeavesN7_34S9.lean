import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h377 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h438 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h3bigk := hb3.1
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
  rcases m.htr 2 3 4 (by decide) (by decide) with h439 | h439
  · linarith only [h12, h439, h9, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h441 | h441
    · linarith only [h377, h441, h9, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h443 | h443
      · rcases m.htr 3 4 5 (by decide) (by decide) with h444 | h444
        · rcases h1bigk with h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h10, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p445_1]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h448 | h448
            · rcases p445_3 (m.d 1 2) (by simp) with h449 | h449
              · linarith only [h0, h449, hlam]
              · linarith only [h449, h9, hlam]
            · linarith only [h448, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h453 | h453
            · rcases p445_3 (m.d 1 2) (by simp) with h454 | h454
              · linarith only [h0, h454, hlam]
              · linarith only [h10, h454, hlam]
            · linarith only [h453, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h458 | h458
            · rcases p445_3 (m.d 1 2) (by simp) with h459 | h459
              · linarith only [h0, h459, hlam]
              · linarith only [h11, h459, hlam]
            · linarith only [h458, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h0, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h465 | h465
            · rcases p445_3 (m.d 1 2) (by simp) with h466 | h466
              · rcases p445_3 (m.d 1 3) (by simp) with h467 | h467
                · linarith only [h467, h9, hlam]
                · rcases p445_3 (m.d 1 4) (by simp) with h469 | h469
                  · linarith only [h10, h469, hlam]
                  · linarith only [h12, h469, hlam]
              · linarith only [h466, h9, hlam]
            · linarith only [h1, h465, hlam]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h0, h10, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p445_1]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h475 | h475
            · rcases p445_3 (m.d 1 2) (by simp) with h476 | h476
              · rcases p445_3 (m.d 1 3) (by simp) with h477 | h477
                · linarith only [h477, h9, hlam]
                · rcases p445_3 (m.d 1 4) (by simp) with h479 | h479
                  · linarith only [h10, h479, hlam]
                  · linarith only [h438, h479, hlam]
              · linarith only [h11, h476, hlam]
            · linarith only [h3, h475, hlam]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h1, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h9, hlam, p445_1]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h12, hlam, p445_1]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h377, hlam, p445_1]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h2, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h10, hlam, p445_1]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h491 | h491
            · rcases p445_3 (m.d 1 2) (by simp) with h492 | h492
              · rcases p445_3 (m.d 1 3) (by simp) with h493 | h493
                · linarith only [h12, h493, hlam]
                · rcases p445_3 (m.d 1 4) (by simp) with h495 | h495
                  · rcases p445_3 (m.d 1 5) (by simp) with h496 | h496
                    · linarith only [h438, h496, hlam]
                    · linarith only [h377, h496, hlam]
                  · linarith only [h12, h495, hlam]
              · linarith only [h492, h9, hlam]
            · linarith only [h1, h491, hlam]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h503 | h503
            · rcases p445_3 (m.d 1 2) (by simp) with h504 | h504
              · rcases p445_3 (m.d 1 3) (by simp) with h505 | h505
                · linarith only [h12, h505, hlam]
                · rcases p445_3 (m.d 1 4) (by simp) with h507 | h507
                  · rcases p445_3 (m.d 1 5) (by simp) with h508 | h508
                    · linarith only [h438, h508, hlam]
                    · rcases h3bigk with h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c | h510c
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h12, h377, h6, hlam, p445_1, p510_2]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h12, h377, h6, h9, hlam, p445_1, p510_2]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h0, h12, h377, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p510_1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        rcases p510_3 (m.d 0 3) (by simp) with h515 | h515
                        · rcases p510_3 (m.d 1 3) (by simp) with h516 | h516
                          · linarith only [h1, h516, hlam]
                          · rcases p510_3 (m.d 2 3) (by simp) with h518 | h518
                            · linarith only [h4, h518, hlam]
                            · rcases p510_3 (m.d 3 4) (by simp) with h520 | h520
                              · linarith only [h520, h6, hlam]
                              · linarith only [h444, h520, hlam]
                        · linarith only [h515, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h1, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h377, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p445_1, p510_1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h12, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h377, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h4, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h9, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h439, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h441, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h6, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        rcases p510_3 (m.d 0 3) (by simp) with h535 | h535
                        · rcases p510_3 (m.d 1 3) (by simp) with h536 | h536
                          · linarith only [h536, hlam, p510_0]
                          · rcases p510_3 (m.d 2 3) (by simp) with h538 | h538
                            · linarith only [h439, h538, hlam]
                            · rcases p510_3 (m.d 3 4) (by simp) with h540 | h540
                              · rcases p510_3 (m.d 3 5) (by simp) with h541 | h541
                                · linarith only [h444, h541, hlam]
                                · linarith only [h377, h541, hlam]
                              · linarith only [h540, hlam, p510_0]
                        · linarith only [h1, h535, hlam]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        rcases p510_3 (m.d 0 3) (by simp) with h546 | h546
                        · rcases p510_3 (m.d 1 3) (by simp) with h547 | h547
                          · linarith only [h12, h547, hlam]
                          · linarith only [h547, h9, hlam]
                        · linarith only [h4, h546, hlam]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h0, h377, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p510_1]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h7, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        rcases p510_3 (m.d 0 3) (by simp) with h554 | h554
                        · rcases p510_3 (m.d 1 3) (by simp) with h555 | h555
                          · linarith only [h555, hlam, p510_0]
                          · rcases p510_3 (m.d 2 3) (by simp) with h557 | h557
                            · linarith only [h441, h557, hlam]
                            · rcases p510_3 (m.d 3 4) (by simp) with h559 | h559
                              · rcases p510_3 (m.d 3 5) (by simp) with h560 | h560
                                · rcases h4bigk with h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p445_1, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    rcases p561_3 (m.d 0 4) (by simp) with h564 | h564
                                    · rcases p561_3 (m.d 1 4) (by simp) with h565 | h565
                                      · linarith only [h2, h565, hlam]
                                      · linarith only [h10, h565, hlam]
                                    · linarith only [h5, h564, hlam]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h12, h377, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    rcases p561_3 (m.d 0 4) (by simp) with h570 | h570
                                    · rcases p561_3 (m.d 1 4) (by simp) with h571 | h571
                                      · linarith only [h2, h571, hlam]
                                      · linarith only [h438, h571, hlam]
                                    · linarith only [h570, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h2, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h2, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h12, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    rcases p561_3 (m.d 0 4) (by simp) with h579 | h579
                                    · rcases p561_3 (m.d 1 4) (by simp) with h580 | h580
                                      · rcases p561_3 (m.d 2 4) (by simp) with h581 | h581
                                        · linarith only [h10, h581, hlam]
                                        · linarith only [h443, h581, hlam]
                                      · linarith only [h580, hlam, p561_0]
                                    · linarith only [h579, h8, hlam]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h5, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h10, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h439, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h10, hc01, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h6, hlam, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h4, h438, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h0, h4, h443, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p561_1]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    rcases p561_3 (m.d 0 4) (by simp) with h595 | h595
                                    · rcases p561_3 (m.d 1 4) (by simp) with h596 | h596
                                      · linarith only [h12, h596, hlam]
                                      · linarith only [h438, h596, hlam]
                                    · linarith only [h595, h8, hlam]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h8, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h438, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h443, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [h444, hlam, p561_0]
                                  · have p561_0 := h561c.1
                                    have p561_1 := h561c.2.1
                                    have p561_2 := h561c.2.2.1
                                    have p561_3 := h561c.2.2.2
                                    linarith only [hlam, p561_0]
                                · linarith only [h560, hlam, p510_0]
                              · linarith only [h12, h559, hlam]
                        · linarith only [h1, h554, hlam]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        rcases p510_3 (m.d 0 3) (by simp) with h608 | h608
                        · rcases p510_3 (m.d 1 3) (by simp) with h609 | h609
                          · linarith only [h377, h609, hlam]
                          · linarith only [h609, h9, hlam]
                        · linarith only [h4, h608, hlam]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [h444, hlam, p510_0]
                      · have p510_0 := h510c.1
                        have p510_1 := h510c.2.1
                        have p510_2 := h510c.2.2.1
                        have p510_3 := h510c.2.2.2
                        linarith only [hlam, p510_0]
                  · linarith only [h438, h507, hlam]
              · linarith only [h11, h504, hlam]
            · linarith only [h3, h503, hlam]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h3, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h11, hlam, p445_1]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            rcases p445_3 (m.d 0 1) (by simp) with h620 | h620
            · rcases p445_3 (m.d 1 2) (by simp) with h621 | h621
              · rcases p445_3 (m.d 1 3) (by simp) with h622 | h622
                · linarith only [h377, h622, hlam]
                · rcases p445_3 (m.d 1 4) (by simp) with h624 | h624
                  · rcases p445_3 (m.d 1 5) (by simp) with h625 | h625
                    · rcases h3bigk with h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h377, h7, hlam, p445_1, p626_2]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h377, h7, h9, hlam, p445_1, p626_2]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h0, h12, h4, h438, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p626_1]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h0, h377, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p626_1]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h1, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h438, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p445_1, p626_1]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h12, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h377, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h4, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h9, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h439, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h441, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h6, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        rcases p626_3 (m.d 0 3) (by simp) with h643 | h643
                        · rcases p626_3 (m.d 1 3) (by simp) with h644 | h644
                          · linarith only [h644, hlam, p626_0]
                          · rcases p626_3 (m.d 2 3) (by simp) with h646 | h646
                            · linarith only [h439, h646, hlam]
                            · rcases p626_3 (m.d 3 4) (by simp) with h648 | h648
                              · rcases p626_3 (m.d 3 5) (by simp) with h649 | h649
                                · linarith only [h444, h649, hlam]
                                · linarith only [h377, h649, hlam]
                              · linarith only [h648, hlam, p626_0]
                        · linarith only [h1, h643, hlam]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        rcases p626_3 (m.d 0 3) (by simp) with h654 | h654
                        · rcases p626_3 (m.d 1 3) (by simp) with h655 | h655
                          · linarith only [h12, h655, hlam]
                          · linarith only [h655, h9, hlam]
                        · linarith only [h4, h654, hlam]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h0, h377, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p626_1]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h7, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        rcases p626_3 (m.d 0 3) (by simp) with h662 | h662
                        · rcases p626_3 (m.d 1 3) (by simp) with h663 | h663
                          · linarith only [h663, hlam, p626_0]
                          · rcases p626_3 (m.d 2 3) (by simp) with h665 | h665
                            · linarith only [h441, h665, hlam]
                            · rcases p626_3 (m.d 3 4) (by simp) with h667 | h667
                              · rcases p626_3 (m.d 3 5) (by simp) with h668 | h668
                                · rcases h4bigk with h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c | h669c
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h438, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    rcases p669_3 (m.d 0 4) (by simp) with h672 | h672
                                    · rcases p669_3 (m.d 1 4) (by simp) with h673 | h673
                                      · linarith only [h2, h673, hlam]
                                      · linarith only [h10, h673, hlam]
                                    · linarith only [h5, h672, hlam]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h0, h12, h4, h438, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p445_1, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    rcases p669_3 (m.d 0 4) (by simp) with h678 | h678
                                    · rcases p669_3 (m.d 1 4) (by simp) with h679 | h679
                                      · linarith only [h2, h679, hlam]
                                      · linarith only [h438, h679, hlam]
                                    · linarith only [h678, hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h2, hlam, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h2, h443, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h12, hlam, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    rcases p669_3 (m.d 0 4) (by simp) with h687 | h687
                                    · rcases p669_3 (m.d 1 4) (by simp) with h688 | h688
                                      · rcases p669_3 (m.d 2 4) (by simp) with h689 | h689
                                        · linarith only [h10, h689, hlam]
                                        · linarith only [h443, h689, hlam]
                                      · linarith only [h688, hlam, p669_0]
                                    · linarith only [h687, h8, hlam]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h5, hlam, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h10, hlam, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h439, hlam, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h0, h10, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h6, hlam, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h0, h4, h438, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h0, h4, h443, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p669_1]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    rcases p669_3 (m.d 0 4) (by simp) with h703 | h703
                                    · rcases p669_3 (m.d 1 4) (by simp) with h704 | h704
                                      · linarith only [h12, h704, hlam]
                                      · linarith only [h438, h704, hlam]
                                    · linarith only [h703, h8, hlam]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h8, hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h438, hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h443, hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [h444, hlam, p669_0]
                                  · have p669_0 := h669c.1
                                    have p669_1 := h669c.2.1
                                    have p669_2 := h669c.2.2.1
                                    have p669_3 := h669c.2.2.2
                                    linarith only [hlam, p669_0]
                                · linarith only [h668, hlam, p626_0]
                              · linarith only [h12, h667, hlam]
                        · linarith only [h1, h662, hlam]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        rcases p626_3 (m.d 0 3) (by simp) with h716 | h716
                        · rcases p626_3 (m.d 1 3) (by simp) with h717 | h717
                          · linarith only [h377, h717, hlam]
                          · linarith only [h717, h9, hlam]
                        · linarith only [h4, h716, hlam]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [h444, hlam, p626_0]
                      · have p626_0 := h626c.1
                        have p626_1 := h626c.2.1
                        have p626_2 := h626c.2.2.1
                        have p626_3 := h626c.2.2.2
                        linarith only [hlam, p626_0]
                    · linarith only [h377, h625, hlam]
                  · linarith only [h12, h624, hlam]
              · linarith only [h621, h9, hlam]
            · linarith only [h1, h620, hlam]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [h438, hlam, p445_0]
          · have p445_0 := h445c.1
            have p445_1 := h445c.2.1
            have p445_2 := h445c.2.2.1
            have p445_3 := h445c.2.2.2
            linarith only [hlam, p445_0]
        · linarith only [h0, h10, h443, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h730 | h730
        · rcases h1bigk with h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c | h731c
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h10, h438, h439, h443, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            rcases p731_3 (m.d 0 1) (by simp) with h734 | h734
            · rcases p731_3 (m.d 1 2) (by simp) with h735 | h735
              · linarith only [h0, h735, hlam]
              · linarith only [h735, h9, hlam]
            · linarith only [h734, hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h438, h439, h443, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            rcases p731_3 (m.d 0 1) (by simp) with h740 | h740
            · rcases p731_3 (m.d 1 2) (by simp) with h741 | h741
              · linarith only [h0, h741, hlam]
              · linarith only [h11, h741, hlam]
            · linarith only [h740, hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h0, hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            rcases p731_3 (m.d 0 1) (by simp) with h747 | h747
            · rcases p731_3 (m.d 1 2) (by simp) with h748 | h748
              · rcases p731_3 (m.d 1 3) (by simp) with h749 | h749
                · linarith only [h749, h9, hlam]
                · rcases p731_3 (m.d 1 4) (by simp) with h751 | h751
                  · linarith only [h10, h751, hlam]
                  · linarith only [h12, h751, hlam]
              · linarith only [h748, h9, hlam]
            · linarith only [h1, h747, hlam]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h0, h438, h439, h443, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h0, h438, h439, h443, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h1, hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h9, hlam, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h12, hlam, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h377, hlam, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h2, hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h10, hlam, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            rcases p731_3 (m.d 0 1) (by simp) with h765 | h765
            · rcases p731_3 (m.d 1 2) (by simp) with h766 | h766
              · rcases p731_3 (m.d 1 3) (by simp) with h767 | h767
                · linarith only [h12, h767, hlam]
                · rcases p731_3 (m.d 1 4) (by simp) with h769 | h769
                  · rcases p731_3 (m.d 1 5) (by simp) with h770 | h770
                    · linarith only [h438, h770, hlam]
                    · linarith only [h377, h770, hlam]
                  · linarith only [h12, h769, hlam]
              · linarith only [h766, h9, hlam]
            · linarith only [h1, h765, hlam]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h12, h438, h439, h443, hc23, hc34, hlam, hphi, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h3, hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h11, hlam, p731_1]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            rcases p731_3 (m.d 0 1) (by simp) with h780 | h780
            · rcases p731_3 (m.d 1 2) (by simp) with h781 | h781
              · rcases p731_3 (m.d 1 3) (by simp) with h782 | h782
                · linarith only [h377, h782, hlam]
                · rcases p731_3 (m.d 1 4) (by simp) with h784 | h784
                  · rcases p731_3 (m.d 1 5) (by simp) with h785 | h785
                    · rcases h3bigk with h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c | h786c
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h377, h7, hlam, p731_1, p786_2]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h377, h7, h9, hlam, p731_1, p786_2]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h0, h12, h4, h438, h439, h443, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p786_1]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h0, h377, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1, p786_1]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h1, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p731_1, p786_1]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h12, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h377, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h4, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h9, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h439, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h441, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h6, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        rcases p786_3 (m.d 0 3) (by simp) with h803 | h803
                        · rcases p786_3 (m.d 1 3) (by simp) with h804 | h804
                          · linarith only [h804, hlam, p786_0]
                          · rcases p786_3 (m.d 2 3) (by simp) with h806 | h806
                            · linarith only [h439, h806, hlam]
                            · rcases p786_3 (m.d 3 4) (by simp) with h808 | h808
                              · rcases p786_3 (m.d 3 5) (by simp) with h809 | h809
                                · linarith only [h730, h809, hlam]
                                · linarith only [h377, h809, hlam]
                              · linarith only [h808, hlam, p786_0]
                        · linarith only [h1, h803, hlam]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        rcases p786_3 (m.d 0 3) (by simp) with h814 | h814
                        · rcases p786_3 (m.d 1 3) (by simp) with h815 | h815
                          · linarith only [h12, h815, hlam]
                          · linarith only [h815, h9, hlam]
                        · linarith only [h4, h814, hlam]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h0, h377, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p786_1]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h7, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        rcases p786_3 (m.d 0 3) (by simp) with h822 | h822
                        · rcases p786_3 (m.d 1 3) (by simp) with h823 | h823
                          · linarith only [h823, hlam, p786_0]
                          · rcases p786_3 (m.d 2 3) (by simp) with h825 | h825
                            · linarith only [h441, h825, hlam]
                            · rcases p786_3 (m.d 3 4) (by simp) with h827 | h827
                              · rcases p786_3 (m.d 3 5) (by simp) with h828 | h828
                                · rcases h4bigk with h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c | h829c
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h438, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    rcases p829_3 (m.d 0 4) (by simp) with h832 | h832
                                    · rcases p829_3 (m.d 1 4) (by simp) with h833 | h833
                                      · linarith only [h2, h833, hlam]
                                      · linarith only [h10, h833, hlam]
                                    · linarith only [h5, h832, hlam]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h12, h438, h9, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p731_1, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    rcases p829_3 (m.d 0 4) (by simp) with h838 | h838
                                    · rcases p829_3 (m.d 1 4) (by simp) with h839 | h839
                                      · linarith only [h2, h839, hlam]
                                      · linarith only [h438, h839, hlam]
                                    · linarith only [h838, hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h2, hlam, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    rcases p829_3 (m.d 0 4) (by simp) with h845 | h845
                                    · rcases p829_3 (m.d 1 4) (by simp) with h846 | h846
                                      · rcases p829_3 (m.d 2 4) (by simp) with h847 | h847
                                        · linarith only [h10, h847, hlam]
                                        · rcases p829_3 (m.d 3 4) (by simp) with h849 | h849
                                          · rcases p829_3 (m.d 4 5) (by simp) with h850 | h850
                                            · linarith only [h438, h850, hlam]
                                            · linarith only [h443, h850, hlam]
                                          · linarith only [h439, h849, hlam]
                                      · linarith only [h10, h846, hlam]
                                    · linarith only [h5, h845, hlam]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h12, hlam, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h12, h439, h443, hc23, hc34, hlam, hphi, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h5, hlam, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h10, hlam, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h439, hlam, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h443, hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h6, hlam, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h0, h4, h438, h439, h443, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    rcases p829_3 (m.d 0 4) (by simp) with h865 | h865
                                    · rcases p829_3 (m.d 1 4) (by simp) with h866 | h866
                                      · linarith only [h12, h866, hlam]
                                      · linarith only [h10, h866, hlam]
                                    · linarith only [h5, h865, hlam]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h0, h4, h439, h443, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h8, hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h438, hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h2, h438, h439, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p829_1]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [h730, hlam, p829_0]
                                  · have p829_0 := h829c.1
                                    have p829_1 := h829c.2.1
                                    have p829_2 := h829c.2.2.1
                                    have p829_3 := h829c.2.2.2
                                    linarith only [hlam, p829_0]
                                · linarith only [h828, hlam, p786_0]
                              · linarith only [h12, h827, hlam]
                        · linarith only [h1, h822, hlam]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        rcases p786_3 (m.d 0 3) (by simp) with h880 | h880
                        · rcases p786_3 (m.d 1 3) (by simp) with h881 | h881
                          · linarith only [h377, h881, hlam]
                          · linarith only [h881, h9, hlam]
                        · linarith only [h4, h880, hlam]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [h730, hlam, p786_0]
                      · have p786_0 := h786c.1
                        have p786_1 := h786c.2.1
                        have p786_2 := h786c.2.2.1
                        have p786_3 := h786c.2.2.2
                        linarith only [hlam, p786_0]
                    · linarith only [h377, h785, hlam]
                  · linarith only [h12, h784, hlam]
              · linarith only [h781, h9, hlam]
            · linarith only [h1, h780, hlam]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [h438, hlam, p731_0]
          · have p731_0 := h731c.1
            have p731_1 := h731c.2.1
            have p731_2 := h731c.2.2.1
            have p731_3 := h731c.2.2.2
            linarith only [hlam, p731_0]
        · linarith only [h12, h438, h730, hlam]

end R2N4
