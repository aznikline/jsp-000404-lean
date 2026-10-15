import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h378 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h439 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h1bigk := hb1.1
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
  have h9 := hg9
  rcases m.htr 2 3 4 (by decide) (by decide) with h440 | h440
  · linarith only [h10, h13, h440, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h442 | h442
    · linarith only [h10, h378, h442, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h444 | h444
      · rcases m.htr 3 4 5 (by decide) (by decide) with h445 | h445
        · rcases h1bigk with h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c | h446c
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h11, h444, hc01, hc45, hlam, hphi, ht0b, ht5b, p446_1]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h449 | h449
            · rcases p446_3 (m.d 1 2) (by simp) with h450 | h450
              · linarith only [h0, h450, hlam]
              · linarith only [h10, h450, hlam]
            · linarith only [h449, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h454 | h454
            · rcases p446_3 (m.d 1 2) (by simp) with h455 | h455
              · linarith only [h0, h455, hlam]
              · linarith only [h11, h455, hlam]
            · linarith only [h454, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h459 | h459
            · rcases p446_3 (m.d 1 2) (by simp) with h460 | h460
              · linarith only [h0, h460, hlam]
              · linarith only [h12, h460, hlam]
            · linarith only [h459, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h0, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h466 | h466
            · rcases p446_3 (m.d 1 2) (by simp) with h467 | h467
              · rcases p446_3 (m.d 1 3) (by simp) with h468 | h468
                · linarith only [h10, h468, hlam]
                · rcases p446_3 (m.d 1 4) (by simp) with h470 | h470
                  · linarith only [h11, h470, hlam]
                  · linarith only [h13, h470, hlam]
              · linarith only [h10, h467, hlam]
            · linarith only [h1, h466, hlam]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h0, h11, h444, hc01, hc45, hlam, hphi, ht0b, ht5b, p446_1]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h476 | h476
            · rcases p446_3 (m.d 1 2) (by simp) with h477 | h477
              · rcases p446_3 (m.d 1 3) (by simp) with h478 | h478
                · linarith only [h10, h478, hlam]
                · rcases p446_3 (m.d 1 4) (by simp) with h480 | h480
                  · linarith only [h11, h480, hlam]
                  · linarith only [h439, h480, hlam]
              · linarith only [h12, h477, hlam]
            · linarith only [h3, h476, hlam]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h1, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h10, hlam, p446_1]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h13, hlam, p446_1]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h378, hlam, p446_1]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h2, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h11, hlam, p446_1]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h492 | h492
            · rcases p446_3 (m.d 1 2) (by simp) with h493 | h493
              · rcases p446_3 (m.d 1 3) (by simp) with h494 | h494
                · linarith only [h13, h494, hlam]
                · rcases p446_3 (m.d 1 4) (by simp) with h496 | h496
                  · rcases p446_3 (m.d 1 5) (by simp) with h497 | h497
                    · linarith only [h439, h497, hlam]
                    · linarith only [h378, h497, hlam]
                  · linarith only [h13, h496, hlam]
              · linarith only [h10, h493, hlam]
            · linarith only [h1, h492, hlam]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h504 | h504
            · rcases p446_3 (m.d 1 2) (by simp) with h505 | h505
              · rcases p446_3 (m.d 1 3) (by simp) with h506 | h506
                · linarith only [h13, h506, hlam]
                · rcases p446_3 (m.d 1 4) (by simp) with h508 | h508
                  · rcases p446_3 (m.d 1 5) (by simp) with h509 | h509
                    · linarith only [h439, h509, hlam]
                    · rcases h3bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h13, h378, h7, hlam, p446_1, p511_2]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h10, h13, h378, h7, hlam, p446_1, p511_2]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h0, h13, h378, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1, p511_1]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        rcases p511_3 (m.d 0 3) (by simp) with h516 | h516
                        · rcases p511_3 (m.d 1 3) (by simp) with h517 | h517
                          · linarith only [h1, h517, hlam]
                          · rcases p511_3 (m.d 2 3) (by simp) with h519 | h519
                            · linarith only [h4, h519, hlam]
                            · rcases p511_3 (m.d 3 4) (by simp) with h521 | h521
                              · linarith only [h521, h7, hlam]
                              · linarith only [h445, h521, hlam]
                        · linarith only [h516, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h1, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h378, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p446_1, p511_1]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h13, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h378, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h4, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h10, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h440, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h442, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h7, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        rcases p511_3 (m.d 0 3) (by simp) with h536 | h536
                        · rcases p511_3 (m.d 1 3) (by simp) with h537 | h537
                          · linarith only [h537, hlam, p511_0]
                          · rcases p511_3 (m.d 2 3) (by simp) with h539 | h539
                            · linarith only [h440, h539, hlam]
                            · rcases p511_3 (m.d 3 4) (by simp) with h541 | h541
                              · rcases p511_3 (m.d 3 5) (by simp) with h542 | h542
                                · linarith only [h445, h542, hlam]
                                · linarith only [h378, h542, hlam]
                              · linarith only [h541, hlam, p511_0]
                        · linarith only [h1, h536, hlam]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        rcases p511_3 (m.d 0 3) (by simp) with h547 | h547
                        · rcases p511_3 (m.d 1 3) (by simp) with h548 | h548
                          · linarith only [h13, h548, hlam]
                          · linarith only [h10, h548, hlam]
                        · linarith only [h4, h547, hlam]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h0, h10, h378, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p511_1]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h8, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        rcases p511_3 (m.d 0 3) (by simp) with h555 | h555
                        · rcases p511_3 (m.d 1 3) (by simp) with h556 | h556
                          · linarith only [h556, hlam, p511_0]
                          · rcases p511_3 (m.d 2 3) (by simp) with h558 | h558
                            · linarith only [h442, h558, hlam]
                            · rcases p511_3 (m.d 3 4) (by simp) with h560 | h560
                              · rcases p511_3 (m.d 3 5) (by simp) with h561 | h561
                                · rcases h5bigk with h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    rcases p562_3 (m.d 0 5) (by simp) with h564 | h564
                                    · rcases p562_3 (m.d 1 5) (by simp) with h565 | h565
                                      · linarith only [h3, h565, hlam]
                                      · rcases p562_3 (m.d 2 5) (by simp) with h567 | h567
                                        · linarith only [h567, h6, hlam]
                                        · rcases p562_3 (m.d 3 5) (by simp) with h569 | h569
                                          · linarith only [h569, h8, hlam]
                                          · linarith only [h378, h569, hlam]
                                    · linarith only [h3, h564, hlam]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    rcases p562_3 (m.d 0 5) (by simp) with h573 | h573
                                    · rcases p562_3 (m.d 1 5) (by simp) with h574 | h574
                                      · linarith only [h3, h574, hlam]
                                      · linarith only [h12, h574, hlam]
                                    · linarith only [h573, h6, hlam]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h0, h10, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p511_1, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    rcases p562_3 (m.d 0 5) (by simp) with h579 | h579
                                    · rcases p562_3 (m.d 1 5) (by simp) with h580 | h580
                                      · linarith only [h3, h580, hlam]
                                      · linarith only [h439, h580, hlam]
                                    · linarith only [h579, h9, hlam]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h3, hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h3, hc01, hc25, hlam, hphi, ht0b, ht5b, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h378, hlam, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h0, h13, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p446_1, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h6, hlam, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h12, hlam, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h442, hlam, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h0, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h8, hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h0, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h0, h4, h445, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p562_1]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h9, hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h439, hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h444, hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [h445, hlam, p562_0]
                                  · have p562_0 := h562c.1
                                    have p562_1 := h562c.2.1
                                    have p562_2 := h562c.2.2.1
                                    have p562_3 := h562c.2.2.2
                                    linarith only [hlam, p562_0]
                                · linarith only [h561, hlam, p511_0]
                              · linarith only [h13, h560, hlam]
                        · linarith only [h1, h555, hlam]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        rcases p511_3 (m.d 0 3) (by simp) with h607 | h607
                        · rcases p511_3 (m.d 1 3) (by simp) with h608 | h608
                          · linarith only [h378, h608, hlam]
                          · linarith only [h10, h608, hlam]
                        · linarith only [h4, h607, hlam]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [h445, hlam, p511_0]
                      · have p511_0 := h511c.1
                        have p511_1 := h511c.2.1
                        have p511_2 := h511c.2.2.1
                        have p511_3 := h511c.2.2.2
                        linarith only [hlam, p511_0]
                  · linarith only [h439, h508, hlam]
              · linarith only [h12, h505, hlam]
            · linarith only [h3, h504, hlam]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h3, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h12, hlam, p446_1]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            rcases p446_3 (m.d 0 1) (by simp) with h619 | h619
            · rcases p446_3 (m.d 1 2) (by simp) with h620 | h620
              · rcases p446_3 (m.d 1 3) (by simp) with h621 | h621
                · linarith only [h378, h621, hlam]
                · rcases p446_3 (m.d 1 4) (by simp) with h623 | h623
                  · rcases p446_3 (m.d 1 5) (by simp) with h624 | h624
                    · rcases h3bigk with h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h378, h445, h7, hlam, p446_1, p625_2]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h10, h378, h445, h7, hlam, p446_1, p625_2]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h0, h378, h4, h445, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h0, h10, h378, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h1, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p446_1, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h13, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h378, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h4, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h10, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h440, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h442, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h7, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        rcases p625_3 (m.d 0 3) (by simp) with h642 | h642
                        · rcases p625_3 (m.d 1 3) (by simp) with h643 | h643
                          · linarith only [h643, hlam, p625_0]
                          · rcases p625_3 (m.d 2 3) (by simp) with h645 | h645
                            · linarith only [h440, h645, hlam]
                            · rcases p625_3 (m.d 3 4) (by simp) with h647 | h647
                              · rcases p625_3 (m.d 3 5) (by simp) with h648 | h648
                                · linarith only [h445, h648, hlam]
                                · linarith only [h378, h648, hlam]
                              · linarith only [h647, hlam, p625_0]
                        · linarith only [h1, h642, hlam]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        rcases p625_3 (m.d 0 3) (by simp) with h653 | h653
                        · rcases p625_3 (m.d 1 3) (by simp) with h654 | h654
                          · linarith only [h13, h654, hlam]
                          · linarith only [h10, h654, hlam]
                        · linarith only [h4, h653, hlam]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h0, h10, h378, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1, p625_1]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h8, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        rcases p625_3 (m.d 0 3) (by simp) with h661 | h661
                        · rcases p625_3 (m.d 1 3) (by simp) with h662 | h662
                          · linarith only [h662, hlam, p625_0]
                          · rcases p625_3 (m.d 2 3) (by simp) with h664 | h664
                            · linarith only [h442, h664, hlam]
                            · rcases p625_3 (m.d 3 4) (by simp) with h666 | h666
                              · rcases p625_3 (m.d 3 5) (by simp) with h667 | h667
                                · rcases h5bigk with h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c | h668c
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h0, h10, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    rcases p668_3 (m.d 0 5) (by simp) with h671 | h671
                                    · rcases p668_3 (m.d 1 5) (by simp) with h672 | h672
                                      · linarith only [h3, h672, hlam]
                                      · linarith only [h12, h672, hlam]
                                    · linarith only [h6, h671, hlam]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h0, h10, h378, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p446_1, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    rcases p668_3 (m.d 0 5) (by simp) with h677 | h677
                                    · rcases p668_3 (m.d 1 5) (by simp) with h678 | h678
                                      · linarith only [h3, h678, hlam]
                                      · linarith only [h439, h678, hlam]
                                    · linarith only [h677, h9, hlam]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h3, hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h378, h442, hc23, hc35, hlam, hphi, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h378, hlam, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h0, h13, h4, h439, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h6, hlam, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h12, hlam, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h442, hlam, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h0, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h8, hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h0, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h0, h4, h445, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p668_1]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h9, hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h439, hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h444, hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [h445, hlam, p668_0]
                                  · have p668_0 := h668c.1
                                    have p668_1 := h668c.2.1
                                    have p668_2 := h668c.2.2.1
                                    have p668_3 := h668c.2.2.2
                                    linarith only [hlam, p668_0]
                                · linarith only [h667, hlam, p625_0]
                              · linarith only [h13, h666, hlam]
                        · linarith only [h1, h661, hlam]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        rcases p625_3 (m.d 0 3) (by simp) with h705 | h705
                        · rcases p625_3 (m.d 1 3) (by simp) with h706 | h706
                          · linarith only [h378, h706, hlam]
                          · linarith only [h10, h706, hlam]
                        · linarith only [h4, h705, hlam]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [h445, hlam, p625_0]
                      · have p625_0 := h625c.1
                        have p625_1 := h625c.2.1
                        have p625_2 := h625c.2.2.1
                        have p625_3 := h625c.2.2.2
                        linarith only [hlam, p625_0]
                    · linarith only [h378, h624, hlam]
                  · linarith only [h13, h623, hlam]
              · linarith only [h10, h620, hlam]
            · linarith only [h1, h619, hlam]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [h439, hlam, p446_0]
          · have p446_0 := h446c.1
            have p446_1 := h446c.2.1
            have p446_2 := h446c.2.2.1
            have p446_3 := h446c.2.2.2
            linarith only [hlam, p446_0]
        · linarith only [h0, h11, h13, h444, h445, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h719 | h719
        · rcases h1bigk with h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h11, h439, h440, h444, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            rcases p720_3 (m.d 0 1) (by simp) with h723 | h723
            · rcases p720_3 (m.d 1 2) (by simp) with h724 | h724
              · linarith only [h0, h724, hlam]
              · linarith only [h10, h724, hlam]
            · linarith only [h723, hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h439, h440, h444, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            rcases p720_3 (m.d 0 1) (by simp) with h729 | h729
            · rcases p720_3 (m.d 1 2) (by simp) with h730 | h730
              · linarith only [h0, h730, hlam]
              · linarith only [h12, h730, hlam]
            · linarith only [h729, hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h0, hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            rcases p720_3 (m.d 0 1) (by simp) with h736 | h736
            · rcases p720_3 (m.d 1 2) (by simp) with h737 | h737
              · rcases p720_3 (m.d 1 3) (by simp) with h738 | h738
                · linarith only [h10, h738, hlam]
                · rcases p720_3 (m.d 1 4) (by simp) with h740 | h740
                  · linarith only [h11, h740, hlam]
                  · linarith only [h13, h740, hlam]
              · linarith only [h10, h737, hlam]
            · linarith only [h1, h736, hlam]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h439, h440, h444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h0, h439, h440, h444, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h1, hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h10, hlam, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h13, hlam, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h378, hlam, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h2, hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h11, hlam, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            rcases p720_3 (m.d 0 1) (by simp) with h754 | h754
            · rcases p720_3 (m.d 1 2) (by simp) with h755 | h755
              · rcases p720_3 (m.d 1 3) (by simp) with h756 | h756
                · linarith only [h13, h756, hlam]
                · rcases p720_3 (m.d 1 4) (by simp) with h758 | h758
                  · rcases p720_3 (m.d 1 5) (by simp) with h759 | h759
                    · linarith only [h439, h759, hlam]
                    · linarith only [h378, h759, hlam]
                  · linarith only [h13, h758, hlam]
              · linarith only [h10, h755, hlam]
            · linarith only [h1, h754, hlam]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h2, h439, h440, h444, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h3, hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h12, hlam, p720_1]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            rcases p720_3 (m.d 0 1) (by simp) with h769 | h769
            · rcases p720_3 (m.d 1 2) (by simp) with h770 | h770
              · rcases p720_3 (m.d 1 3) (by simp) with h771 | h771
                · linarith only [h378, h771, hlam]
                · rcases p720_3 (m.d 1 4) (by simp) with h773 | h773
                  · rcases p720_3 (m.d 1 5) (by simp) with h774 | h774
                    · rcases h3bigk with h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c | h775c
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h13, h439, h7, hlam, p720_1, p775_2]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h10, h13, h439, h7, hlam, p720_1, p775_2]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h0, h13, h4, h439, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1, p775_1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h0, h378, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1, p775_1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h1, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h439, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p720_1, p775_1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h13, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h378, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h4, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h10, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h440, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h442, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h7, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        rcases p775_3 (m.d 0 3) (by simp) with h792 | h792
                        · rcases p775_3 (m.d 1 3) (by simp) with h793 | h793
                          · linarith only [h793, hlam, p775_0]
                          · rcases p775_3 (m.d 2 3) (by simp) with h795 | h795
                            · linarith only [h440, h795, hlam]
                            · rcases p775_3 (m.d 3 4) (by simp) with h797 | h797
                              · rcases p775_3 (m.d 3 5) (by simp) with h798 | h798
                                · linarith only [h719, h798, hlam]
                                · linarith only [h378, h798, hlam]
                              · linarith only [h797, hlam, p775_0]
                        · linarith only [h1, h792, hlam]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        rcases p775_3 (m.d 0 3) (by simp) with h803 | h803
                        · rcases p775_3 (m.d 1 3) (by simp) with h804 | h804
                          · linarith only [h13, h804, hlam]
                          · linarith only [h10, h804, hlam]
                        · linarith only [h4, h803, hlam]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h0, h378, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p775_1]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h8, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        rcases p775_3 (m.d 0 3) (by simp) with h811 | h811
                        · rcases p775_3 (m.d 1 3) (by simp) with h812 | h812
                          · linarith only [h812, hlam, p775_0]
                          · rcases p775_3 (m.d 2 3) (by simp) with h814 | h814
                            · linarith only [h442, h814, hlam]
                            · rcases p775_3 (m.d 3 4) (by simp) with h816 | h816
                              · rcases p775_3 (m.d 3 5) (by simp) with h817 | h817
                                · rcases h5bigk with h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h0, h10, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    rcases p818_3 (m.d 0 5) (by simp) with h821 | h821
                                    · rcases p818_3 (m.d 1 5) (by simp) with h822 | h822
                                      · linarith only [h3, h822, hlam]
                                      · linarith only [h12, h822, hlam]
                                    · linarith only [h6, h821, hlam]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h0, h10, h378, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p720_1, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h0, h4, h440, h444, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h3, hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h378, h440, h444, hc23, hc35, hlam, hphi, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h378, hlam, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h0, h13, h4, h439, h440, h444, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h6, hlam, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h12, hlam, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h442, hlam, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h444, hlam, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h8, hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h0, h4, h440, h444, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h0, h4, h440, h444, h7, h719, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h9, hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h439, hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h440, h444, hc23, hc45, hlam, hphi, ht34, p818_1]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [h719, hlam, p818_0]
                                  · have p818_0 := h818c.1
                                    have p818_1 := h818c.2.1
                                    have p818_2 := h818c.2.2.1
                                    have p818_3 := h818c.2.2.2
                                    linarith only [hlam, p818_0]
                                · linarith only [h817, hlam, p775_0]
                              · linarith only [h13, h816, hlam]
                        · linarith only [h1, h811, hlam]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        rcases p775_3 (m.d 0 3) (by simp) with h851 | h851
                        · rcases p775_3 (m.d 1 3) (by simp) with h852 | h852
                          · linarith only [h378, h852, hlam]
                          · linarith only [h10, h852, hlam]
                        · linarith only [h4, h851, hlam]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [h719, hlam, p775_0]
                      · have p775_0 := h775c.1
                        have p775_1 := h775c.2.1
                        have p775_2 := h775c.2.2.1
                        have p775_3 := h775c.2.2.2
                        linarith only [hlam, p775_0]
                    · linarith only [h378, h774, hlam]
                  · linarith only [h13, h773, hlam]
              · linarith only [h10, h770, hlam]
            · linarith only [h1, h769, hlam]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [h439, hlam, p720_0]
          · have p720_0 := h720c.1
            have p720_1 := h720c.2.1
            have p720_2 := h720c.2.2.1
            have p720_3 := h720c.2.2.2
            linarith only [hlam, p720_0]
        · linarith only [h13, h439, h719, hlam]

end R2N4
