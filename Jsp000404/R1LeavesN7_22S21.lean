import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5526000 in
set_option maxHeartbeats 5526000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s5_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3977 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4846 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5465 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h5466 | h5466
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5467 | h5467
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5468 | h5468
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5469 | h5469
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5470 | h5470
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5471 | h5471
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5472 | h5472
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5473 | h5473
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5474 | h5474
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5475 | h5475
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5476 | h5476
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5477 | h5477
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5478 | h5478
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5479 | h5479
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5480 | h5480
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5481 | h5481
                                · linarith only [h5466, h5478, h5481, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h2bigk with h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h0, hlam, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h0, h5478, h5480, h5481, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h0, h5480, h5481, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    rcases p5483_3 (m.d 0 2) (by simp) with h5488 | h5488
                                    · rcases p5483_3 (m.d 1 2) (by simp) with h5489 | h5489
                                      · rcases p5483_3 (m.d 2 3) (by simp) with h5490 | h5490
                                        · linarith only [h5466, h5490, hlam]
                                        · linarith only [h5479, h5490, hlam]
                                      · linarith only [h5474, h5489, hlam]
                                    · linarith only [h5488, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p5483_1, u0ehi1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5478, h5480, h5481, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5480, h5481, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    rcases p5483_3 (m.d 0 2) (by simp) with h5499 | h5499
                                    · linarith only [h0, h5499, hlam]
                                    · linarith only [h5468, h5499, hlam]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5466, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5472, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5466, h5480, h5481, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h0, h5466, h5480, h5481, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5467, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5473, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5478, hlam, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h0, h5467, h5480, h5481, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5468, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5474, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5479, hlam, p5483_1]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [h5480, hlam, p5483_0]
                                  · have p5483_0 := h5483c.1
                                    have p5483_1 := h5483c.2.1
                                    have p5483_2 := h5483c.2.2.1
                                    have p5483_3 := h5483c.2.2.2
                                    linarith only [hlam, p5483_0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5517 | h5517
                                · linarith only [h0, h5466, h5478, h5480, h5517, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h2bigk with h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c | h5519c
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h0, hlam, p5519_1]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h0, h5479, hc12, hlam, hphi, ht01, ht0b, ht5b, p5519_1, u5ehi3]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    rcases p5519_3 (m.d 0 2) (by simp) with h5523 | h5523
                                    · rcases p5519_3 (m.d 1 2) (by simp) with h5524 | h5524
                                      · rcases p5519_3 (m.d 2 3) (by simp) with h5525 | h5525
                                        · linarith only [h5466, h5525, hlam]
                                        · linarith only [h5478, h5525, hlam]
                                      · linarith only [h5473, h5524, hlam]
                                    · linarith only [h5523, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    rcases p5519_3 (m.d 0 2) (by simp) with h5530 | h5530
                                    · rcases p5519_3 (m.d 1 2) (by simp) with h5531 | h5531
                                      · rcases p5519_3 (m.d 2 3) (by simp) with h5532 | h5532
                                        · linarith only [h5466, h5532, hlam]
                                        · linarith only [h5479, h5532, hlam]
                                      · linarith only [h5474, h5531, hlam]
                                    · linarith only [h5530, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p5519_1, u0ehi1]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5479, hc12, hlam, hphi, ht01, ht0b, ht5b, p5519_1, u5ehi3]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5475, h5477, h5480, hlam, p5519_2]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    rcases p5519_3 (m.d 0 2) (by simp) with h5541 | h5541
                                    · linarith only [h0, h5541, hlam]
                                    · linarith only [h5468, h5541, hlam]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5466, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5472, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    rcases p5519_3 (m.d 0 2) (by simp) with h5547 | h5547
                                    · rcases p5519_3 (m.d 1 2) (by simp) with h5548 | h5548
                                      · rcases p5519_3 (m.d 2 3) (by simp) with h5549 | h5549
                                        · rcases p5519_3 (m.d 2 4) (by simp) with h5550 | h5550
                                          · linarith only [h5478, h5550, hlam]
                                          · rcases p5519_3 (m.d 2 5) (by simp) with h5552 | h5552
                                            · linarith only [h5479, h5552, hlam]
                                            · linarith only [h5480, h5552, hlam]
                                        · linarith only [h5478, h5549, hlam]
                                      · linarith only [h5473, h5548, hlam]
                                    · linarith only [h5467, h5547, hlam]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5466, hc02, hlam, hphi, ht0b, ht5b, p5519_1, u5ehi2]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5467, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5473, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5478, hlam, p5519_1]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5480, hlam, p5519_1]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5468, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5474, hlam, p5519_0]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h5479, hlam, p5519_1]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5474, h5475, h5478, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5519_1]
                                  · have p5519_0 := h5519c.1
                                    have p5519_1 := h5519c.2.1
                                    have p5519_2 := h5519c.2.2.1
                                    have p5519_3 := h5519c.2.2.2
                                    linarith only [hlam, p5519_0]
                            · linarith only [h4846, h5465, h5472, h5475, h5476, h5478, h5479, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5570 | h5570
                            · linarith only [h3977, h5469, h5472, h5478, h5570, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5572 | h5572
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5573 | h5573
                                · rcases h2bigk with h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c | h5574c
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h0, hlam, p5574_1]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    rcases p5574_3 (m.d 0 2) (by simp) with h5577 | h5577
                                    · rcases p5574_3 (m.d 1 2) (by simp) with h5578 | h5578
                                      · rcases p5574_3 (m.d 2 3) (by simp) with h5579 | h5579
                                        · linarith only [h5579, hlam, p5574_0]
                                        · rcases p5574_3 (m.d 2 4) (by simp) with h5581 | h5581
                                          · linarith only [h5467, h5581, hlam]
                                          · linarith only [h5478, h5581, hlam]
                                      · linarith only [h5472, h5578, hlam]
                                    · linarith only [h5577, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5572, hc02, hlam, hphi, ht0b, ht5b, p5574_1, u5ehi4]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    rcases p5574_3 (m.d 0 2) (by simp) with h5587 | h5587
                                    · rcases p5574_3 (m.d 1 2) (by simp) with h5588 | h5588
                                      · rcases p5574_3 (m.d 2 3) (by simp) with h5589 | h5589
                                        · linarith only [h5466, h5589, hlam]
                                        · rcases p5574_3 (m.d 2 4) (by simp) with h5591 | h5591
                                          · linarith only [h5467, h5591, hlam]
                                          · linarith only [h5572, h5591, hlam]
                                      · linarith only [h5474, h5588, hlam]
                                    · linarith only [h5587, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p5574_1, u0ehi1]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5475, h5476, h5570, hlam, p5574_2]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5572, hc12, hlam, hphi, ht01, ht0b, ht5b, p5574_1, u5ehi4]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    rcases p5574_3 (m.d 0 2) (by simp) with h5600 | h5600
                                    · linarith only [h0, h5600, hlam]
                                    · linarith only [h5468, h5600, hlam]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5466, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5472, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5478, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5570, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5467, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5473, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    rcases p5574_3 (m.d 0 2) (by simp) with h5610 | h5610
                                    · rcases p5574_3 (m.d 1 2) (by simp) with h5611 | h5611
                                      · rcases p5574_3 (m.d 2 3) (by simp) with h5612 | h5612
                                        · linarith only [h5478, h5612, hlam]
                                        · rcases p5574_3 (m.d 2 4) (by simp) with h5614 | h5614
                                          · rcases p5574_3 (m.d 2 5) (by simp) with h5615 | h5615
                                            · linarith only [h5572, h5615, hlam]
                                            · linarith only [h5570, h5615, hlam]
                                          · linarith only [h5478, h5614, hlam]
                                      · linarith only [h5472, h5611, hlam]
                                    · linarith only [h5466, h5610, hlam]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5466, h5469, h5478, hc02, hlam, hphi, ht0b, ht5b, p5574_1, u5ehi2]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5468, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5474, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5474, h5475, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5574_1]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [h5572, hlam, p5574_0]
                                  · have p5574_0 := h5574c.1
                                    have p5574_1 := h5574c.2.1
                                    have p5574_2 := h5574c.2.2.1
                                    have p5574_3 := h5574c.2.2.2
                                    linarith only [hlam, p5574_0]
                                · linarith only [h4846, h5465, h5472, h5475, h5477, h5478, h5573, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5629 | h5629
                                · rcases h2bigk with h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c | h5630c
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h0, hlam, p5630_1]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5466, h5469, h5478, h5572, h5629, hlam, p5630_2]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5466, h5469, h5572, h5629, hlam, p5630_2]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    rcases p5630_3 (m.d 0 2) (by simp) with h5635 | h5635
                                    · rcases p5630_3 (m.d 1 2) (by simp) with h5636 | h5636
                                      · rcases p5630_3 (m.d 2 3) (by simp) with h5637 | h5637
                                        · linarith only [h5466, h5637, hlam]
                                        · rcases p5630_3 (m.d 2 4) (by simp) with h5639 | h5639
                                          · linarith only [h5467, h5639, hlam]
                                          · rcases p5630_3 (m.d 2 5) (by simp) with h5641 | h5641
                                            · linarith only [h5641, hlam, p5630_0]
                                            · rcases h3bigk with h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c | h5643c
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h3977, hlam, p5643_1]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5469, h5478, h5572, h5629, hlam, p5643_2]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5466, h5478, h5572, h5629, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5643_1]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                rcases p5643_3 (m.d 0 3) (by simp) with h5648 | h5648
                                                · rcases p5643_3 (m.d 1 3) (by simp) with h5649 | h5649
                                                  · rcases p5643_3 (m.d 2 3) (by simp) with h5650 | h5650
                                                    · linarith only [h5466, h5650, hlam]
                                                    · rcases p5643_3 (m.d 3 4) (by simp) with h5652 | h5652
                                                      · linarith only [h5469, h5652, hlam]
                                                      · linarith only [h5629, h5652, hlam]
                                                  · linarith only [h5476, h5649, hlam]
                                                · linarith only [h5648, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [hc13, hlam, hphi, ht01, p5643_1, u0ehi2]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h3977, h5465, h5476, h5478, h5572, h5629, hlam, p5643_2]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5478, h5572, h5629, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5643_1]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                rcases p5643_3 (m.d 0 3) (by simp) with h5661 | h5661
                                                · linarith only [h3977, h5661, hlam]
                                                · linarith only [h5470, h5661, hlam]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5466, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5472, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5478, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5570, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5469, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5475, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                rcases p5643_3 (m.d 0 3) (by simp) with h5671 | h5671
                                                · rcases p5643_3 (m.d 1 3) (by simp) with h5672 | h5672
                                                  · rcases p5643_3 (m.d 2 3) (by simp) with h5673 | h5673
                                                    · linarith only [h5673, hlam, p5643_0]
                                                    · rcases p5643_3 (m.d 3 4) (by simp) with h5675 | h5675
                                                      · rcases p5643_3 (m.d 3 5) (by simp) with h5676 | h5676
                                                        · linarith only [h5629, h5676, hlam]
                                                        · linarith only [h5570, h5676, hlam]
                                                      · linarith only [h5675, hlam, p5643_0]
                                                  · linarith only [h5472, h5672, hlam]
                                                · linarith only [h5466, h5671, hlam]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5469, h5478, h5572, h5629, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5643_1]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5470, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5476, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h4846, h5465, h5476, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5643_1]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [h5629, hlam, p5643_0]
                                              · have p5643_0 := h5643c.1
                                                have p5643_1 := h5643c.2.1
                                                have p5643_2 := h5643c.2.2.1
                                                have p5643_3 := h5643c.2.2.2
                                                linarith only [hlam, p5643_0]
                                      · linarith only [h5474, h5636, hlam]
                                    · linarith only [h5635, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p5630_1, u0ehi1]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5475, h5476, h5570, hlam, p5630_2]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5475, h5476, h5572, h5629, hlam, p5630_2]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    rcases p5630_3 (m.d 0 2) (by simp) with h5695 | h5695
                                    · linarith only [h0, h5695, hlam]
                                    · linarith only [h5468, h5695, hlam]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5466, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5472, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5478, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5570, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5467, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5473, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5475, h5476, h5572, h5629, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5630_1]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5572, hlam, p5630_1]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5468, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h5474, hlam, p5630_0]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5474, h5475, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5630_1]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [h4846, h5465, h5472, h5475, h5476, h5572, h5629, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p5630_1]
                                  · have p5630_0 := h5630c.1
                                    have p5630_1 := h5630c.2.1
                                    have p5630_2 := h5630c.2.2.1
                                    have p5630_3 := h5630c.2.2.2
                                    linarith only [hlam, p5630_0]
                                · linarith only [h4846, h5465, h5472, h5475, h5477, h5478, h5629, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h4846, h5465, h5477, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h4846, h5465, h5475, h5476, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h3977, h5465, h5475, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                  · linarith only [h3977, h5465, h5472, h5474, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h3977, h5465, h5472, h5473, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h5465, h5472, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h4846, h5465, h5471, hlam]
          · linarith only [h3977, h5465, h5470, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5722 | h5722
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5723 | h5723
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5724 | h5724
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5725 | h5725
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5726 | h5726
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5727 | h5727
                    · linarith only [h3977, h5465, h5469, h5724, h5726, h5727, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h3977, h5465, h5726, h5727, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h0, h5465, h5726, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h3977, h5465, h5467, h5724, h5725, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h5465, h5724, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h3977, h5465, h5469, h5723, hlam]
          · linarith only [h3977, h5465, h5722, hlam]
      · linarith only [h0, h5465, h5468, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5736 | h5736
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5737 | h5737
        · linarith only [h5466, h5467, h5737, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5739 | h5739
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5740 | h5740
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5741 | h5741
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5742 | h5742
                · linarith only [h3977, h5465, h5466, h5467, h5742, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h5465, h5742, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h5465, h5466, h5741, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
            · linarith only [h0, h5465, h5467, h5740, hlam]
          · linarith only [h3977, h5465, h5739, hlam]
      · linarith only [h3977, h5465, h5466, h5736, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5749 | h5749
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5750 | h5750
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5751 | h5751
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5752 | h5752
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5753 | h5753
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5754 | h5754
              · linarith only [h5466, h5750, h5754, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h5465, h5754, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h4846, h5465, h5753, hlam]
          · linarith only [h4846, h5465, h5466, h5749, h5752, hlam]
        · linarith only [h5466, h5749, h5751, hlam]
      · linarith only [h4846, h5465, h5749, h5750, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5761 | h5761
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5762 | h5762
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5763 | h5763
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5764 | h5764
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5765 | h5765
              · linarith only [h5466, h5761, h5765, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h5465, h5765, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h0, h5465, h5749, h5764, hlam]
          · linarith only [h0, h5465, h5749, h5762, h5763, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5770 | h5770
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5771 | h5771
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5772 | h5772
              · linarith only [h0, h5465, h5466, h5772, hc12, hlam, hphi, ht01, u0ehi4]
              · linarith only [h0, h5465, h5772, hc23, hlam, hphi, ht01, ht12, u0ehi4]
            · linarith only [h3977, h5465, h5762, h5771, hlam]
          · linarith only [h0, h5465, h5466, h5770, hlam]
      · linarith only [h0, h5465, h5761, hlam]

end R2N4
