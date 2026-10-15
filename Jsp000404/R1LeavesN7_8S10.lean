import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S5
import Jsp000404.R1LeavesN7_8S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6350000 in
set_option maxHeartbeats 6350000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s7 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h3476 | h3476
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3477 | h3477
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3478 | h3478
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3479 | h3479
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3480 | h3480
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3481 | h3481
            · linarith only [h0, h3481, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3483 | h3483
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3484 | h3484
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3485 | h3485
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3486 | h3486
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3487 | h3487
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3488 | h3488
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3489 | h3489
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3490 | h3490
                            · linarith only [h0, h3483, h3490, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3492 | h3492
                              · linarith only [h3488, h3490, h3492, hlam]
                              · rcases h0bigk with h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c | h3494c
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h2, h3476, h3487, h3488, h3490, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h2, h3476, h3487, h3488, h3490, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h2, h3487, h3488, h3490, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  rcases p3494_3 (m.d 0 1) (by simp) with h3499 | h3499
                                  · rcases p3494_3 (m.d 0 2) (by simp) with h3500 | h3500
                                    · linarith only [h0, h3500, hlam]
                                    · linarith only [h3477, h3500, hlam]
                                  · linarith only [h3, h3499, hlam]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h0, hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h4, hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h2, h3487, h3488, h3490, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3494_1, u5ehi0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h1, hlam, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h2, h3476, h3487, h3488, h3490, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h2, h3487, h3488, h3490, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  rcases p3494_3 (m.d 0 1) (by simp) with h3513 | h3513
                                  · rcases p3494_3 (m.d 0 2) (by simp) with h3514 | h3514
                                    · linarith only [h3514, h4, hlam]
                                    · linarith only [h3477, h3514, hlam]
                                  · linarith only [h3, h3513, hlam]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h2, hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h3476, hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h3478, hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h3, h3476, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3494_1, u5ehi1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h3, hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h3477, hlam, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h3479, hlam, p3494_0]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [h3480, hlam, p3494_1]
                                · have p3494_0 := h3494c.1
                                  have p3494_1 := h3494c.2.1
                                  have p3494_2 := h3494c.2.2.1
                                  have p3494_3 := h3494c.2.2.2
                                  linarith only [hlam, p3494_0]
                          · linarith only [h3477, h3489, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h2, h3476, h3487, h3488, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3530 | h3530
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3531 | h3531
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3532 | h3532
                            · linarith only [h3483, h3487, h3532, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3534 | h3534
                              · linarith only [h3483, h3487, h3530, h3534, hlam]
                              · rcases h0bigk with h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c | h3536c
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3476, h3480, h3487, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3476, h3480, h3483, h3487, h3530, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3480, h3483, h3487, h3530, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  rcases p3536_3 (m.d 0 1) (by simp) with h3541 | h3541
                                  · rcases p3536_3 (m.d 0 2) (by simp) with h3542 | h3542
                                    · linarith only [h0, h3542, hlam]
                                    · linarith only [h3477, h3542, hlam]
                                  · linarith only [h3, h3541, hlam]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h0, hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h4, hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3480, h3483, h3487, h3530, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3480, h3483, h3487, h3530, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h1, hlam, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3476, h3480, h3483, h3487, h3530, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3480, h3483, h3487, h3530, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  rcases p3536_3 (m.d 0 1) (by simp) with h3555 | h3555
                                  · rcases p3536_3 (m.d 0 2) (by simp) with h3556 | h3556
                                    · linarith only [h3556, h4, hlam]
                                    · linarith only [h3477, h3556, hlam]
                                  · linarith only [h3, h3555, hlam]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h2, hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3476, hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3478, hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3476, h3480, h3483, h3487, h3530, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3, hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3477, hlam, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3479, hlam, p3536_0]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [h3480, hlam, p3536_1]
                                · have p3536_0 := h3536c.1
                                  have p3536_1 := h3536c.2.1
                                  have p3536_2 := h3536c.2.2.1
                                  have p3536_3 := h3536c.2.2.2
                                  linarith only [hlam, p3536_0]
                          · linarith only [h3477, h3531, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h3476, h3480, h3483, h3487, h3530, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h3476, h3479, h3480, h3481, h3484, h3486, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h3478, h3481, h3484, h3485, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h3477, h3484, h4, hc12, hc23, hlam, hphi]
              · linarith only [h3476, h3483, h4, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3576 | h3576
            · linarith only [h3477, h3576, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3578 | h3578
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3579 | h3579
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3580 | h3580
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3581 | h3581
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3582 | h3582
                      · linarith only [h2, h3480, h3582, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3584 | h3584
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3585 | h3585
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3586 | h3586
                            · linarith only [h2, h3480, h3578, h3586, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3588 | h3588
                              · linarith only [h0, h3579, h3584, h3586, h3588, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases h0bigk with h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c | h3590c
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h0, h3579, hc01, hlam, hphi, ht0b, ht5b, p3590_1, u5ehi2]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h1, h3576, h3579, h3585, hc01, hlam, hphi, ht0b, ht5b, p3590_1, u5ehi3]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 1) (by simp) with h3594 | h3594
                                  · rcases p3590_3 (m.d 0 2) (by simp) with h3595 | h3595
                                    · linarith only [h0, h3595, hlam]
                                    · linarith only [h3476, h3595, hlam]
                                  · linarith only [h2, h3594, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 1) (by simp) with h3599 | h3599
                                  · rcases p3590_3 (m.d 0 2) (by simp) with h3600 | h3600
                                    · linarith only [h0, h3600, hlam]
                                    · linarith only [h3477, h3600, hlam]
                                  · linarith only [h3, h3599, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h0, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h4, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 1) (by simp) with h3607 | h3607
                                  · rcases p3590_3 (m.d 0 2) (by simp) with h3608 | h3608
                                    · rcases p3590_3 (m.d 0 3) (by simp) with h3609 | h3609
                                      · rcases p3590_3 (m.d 0 4) (by simp) with h3610 | h3610
                                        · linarith only [h3476, h3610, hlam]
                                        · rcases p3590_3 (m.d 0 5) (by simp) with h3612 | h3612
                                          · linarith only [h3477, h3612, hlam]
                                          · linarith only [h3480, h3612, hlam]
                                      · linarith only [h3478, h3609, hlam]
                                    · linarith only [h3476, h3608, hlam]
                                  · linarith only [h2, h3607, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3590_1, u5ehi0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h1, hlam, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h0, h3579, h3585, hc03, hlam, hphi, ht0b, ht5b, p3590_1, u5ehi3]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 1) (by simp) with h3622 | h3622
                                  · rcases p3590_3 (m.d 0 2) (by simp) with h3623 | h3623
                                    · linarith only [h3623, h4, hlam]
                                    · linarith only [h3476, h3623, hlam]
                                  · linarith only [h2, h3622, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 1) (by simp) with h3627 | h3627
                                  · rcases p3590_3 (m.d 0 2) (by simp) with h3628 | h3628
                                    · linarith only [h3628, h4, hlam]
                                    · linarith only [h3477, h3628, hlam]
                                  · linarith only [h3, h3627, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h2, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3476, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3478, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3480, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3477, hlam, p3590_1]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [h3479, hlam, p3590_0]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  rcases p3590_3 (m.d 0 1) (by simp) with h3640 | h3640
                                  · rcases p3590_3 (m.d 0 2) (by simp) with h3641 | h3641
                                    · rcases p3590_3 (m.d 0 3) (by simp) with h3642 | h3642
                                      · rcases p3590_3 (m.d 0 4) (by simp) with h3643 | h3643
                                        · linarith only [h3480, h3643, hlam]
                                        · rcases p3590_3 (m.d 0 5) (by simp) with h3645 | h3645
                                          · rcases h2bigk with h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c | h3646c
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3579, h3585, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3646_1, u5ehi3]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h4, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              rcases p3646_3 (m.d 0 2) (by simp) with h3650 | h3650
                                              · rcases p3646_3 (m.d 1 2) (by simp) with h3651 | h3651
                                                · linarith only [h0, h3651, hlam]
                                                · linarith only [h3578, h3651, hlam]
                                              · linarith only [h3650, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3585, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3646_1, u5ehi3]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h0, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3576, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              rcases p3646_3 (m.d 0 2) (by simp) with h3659 | h3659
                                              · rcases p3646_3 (m.d 1 2) (by simp) with h3660 | h3660
                                                · rcases p3646_3 (m.d 2 3) (by simp) with h3661 | h3661
                                                  · rcases p3646_3 (m.d 2 4) (by simp) with h3662 | h3662
                                                    · linarith only [h3662, hlam, p3646_0]
                                                    · rcases p3646_3 (m.d 2 5) (by simp) with h3664 | h3664
                                                      · linarith only [h3579, h3664, hlam]
                                                      · linarith only [h3586, h3664, hlam]
                                                  · linarith only [h3584, h3661, hlam]
                                                · linarith only [h3660, hlam, p3646_0]
                                              · linarith only [h3476, h3659, hlam]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h0, h3585, hc01, hlam, hphi, ht0b, ht5b, p3646_1, u5ehi3]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3477, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3590_1, p3646_1]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3579, h3585, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3646_1, u5ehi3]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h2, h3477, h3578, h4, hlam, p3590_1, p3646_2]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              rcases p3646_3 (m.d 0 2) (by simp) with h3675 | h3675
                                              · linarith only [h3675, h4, hlam]
                                              · linarith only [h3477, h3675, hlam]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3476, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3578, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3584, hlam, p3646_1]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3586, hlam, p3646_1]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3477, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3579, hlam, p3646_0]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h3585, hlam, p3646_1]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [h0, h3579, h3584, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3646_1]
                                            · have p3646_0 := h3646c.1
                                              have p3646_1 := h3646c.2.1
                                              have p3646_2 := h3646c.2.2.1
                                              have p3646_3 := h3646c.2.2.2
                                              linarith only [hlam, p3646_0]
                                          · linarith only [h3480, h3645, hlam]
                                      · linarith only [h3478, h3642, hlam]
                                    · linarith only [h3476, h3641, hlam]
                                  · linarith only [h2, h3640, hlam]
                                · have p3590_0 := h3590c.1
                                  have p3590_1 := h3590c.2.1
                                  have p3590_2 := h3590c.2.2.1
                                  have p3590_3 := h3590c.2.2.2
                                  linarith only [hlam, p3590_0]
                          · linarith only [h0, h3579, h3585, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                        · linarith only [h0, h3579, h3584, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h3477, h3479, h3576, h3579, h3581, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h3477, h3478, h3480, h3576, h3579, h3580, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h3477, h3579, h4, hc12, hc23, hlam, hphi]
              · linarith only [h3476, h3578, h4, hc12, hc23, hlam, hphi]
        · linarith only [h3477, h3479, h4, hlam]
      · linarith only [h3476, h3478, h4, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3701 | h3701
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3702 | h3702
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3703 | h3703
          · linarith only [h3476, h3477, h3703, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3705 | h3705
            · linarith only [h0, h3705, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3707 | h3707
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3708 | h3708
                · linarith only [h0, h3477, h3708, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3710 | h3710
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3711 | h3711
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3712 | h3712
                      · linarith only [h2, h3703, h3712, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3714 | h3714
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3715 | h3715
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3716 | h3716
                            · linarith only [h0, h2, h3477, h3703, h3707, h3715, h3716, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3718 | h3718
                              · linarith only [h0, h3477, h3707, h3714, h3716, h3718, hlam]
                              · rcases h0bigk with h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c | h3720c
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  rcases p3720_3 (m.d 0 1) (by simp) with h3722 | h3722
                                  · rcases p3720_3 (m.d 0 2) (by simp) with h3723 | h3723
                                    · linarith only [h0, h3723, hlam]
                                    · rcases p3720_3 (m.d 0 3) (by simp) with h3725 | h3725
                                      · linarith only [h1, h3725, hlam]
                                      · linarith only [h3725, h4, hlam]
                                  · linarith only [h0, h3722, hlam]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h1, h3711, hc01, hlam, hphi, ht0b, ht5b, p3720_1, u5ehi3]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  rcases p3720_3 (m.d 0 1) (by simp) with h3730 | h3730
                                  · rcases p3720_3 (m.d 0 2) (by simp) with h3731 | h3731
                                    · linarith only [h0, h3731, hlam]
                                    · linarith only [h3476, h3731, hlam]
                                  · linarith only [h2, h3730, hlam]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  rcases p3720_3 (m.d 0 1) (by simp) with h3735 | h3735
                                  · rcases p3720_3 (m.d 0 2) (by simp) with h3736 | h3736
                                    · linarith only [h0, h3736, hlam]
                                    · rcases p3720_3 (m.d 0 3) (by simp) with h3738 | h3738
                                      · linarith only [h1, h3738, hlam]
                                      · linarith only [h3702, h3738, hlam]
                                  · linarith only [h3, h3735, hlam]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h0, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h4, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h2, h3477, h3707, h3714, h3716, hc34, hc45, hlam, hphi, p3720_1]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h3477, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h1, hlam, p3720_1]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  rcases p3720_3 (m.d 0 1) (by simp) with h3748 | h3748
                                  · rcases p3720_3 (m.d 0 2) (by simp) with h3749 | h3749
                                    · linarith only [h3749, h4, hlam]
                                    · rcases p3720_3 (m.d 0 3) (by simp) with h3751 | h3751
                                      · rcases p3720_3 (m.d 0 4) (by simp) with h3752 | h3752
                                        · linarith only [h3701, h3752, hlam]
                                        · rcases p3720_3 (m.d 0 5) (by simp) with h3754 | h3754
                                          · linarith only [h3702, h3754, hlam]
                                          · linarith only [h3477, h3754, hlam]
                                      · linarith only [h3751, h4, hlam]
                                  · linarith only [h0, h3748, hlam]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  rcases p3720_3 (m.d 0 1) (by simp) with h3760 | h3760
                                  · rcases p3720_3 (m.d 0 2) (by simp) with h3761 | h3761
                                    · linarith only [h3761, h4, hlam]
                                    · linarith only [h3476, h3761, hlam]
                                  · linarith only [h2, h3760, hlam]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  rcases p3720_3 (m.d 0 1) (by simp) with h3765 | h3765
                                  · rcases p3720_3 (m.d 0 2) (by simp) with h3766 | h3766
                                    · linarith only [h3766, h4, hlam]
                                    · rcases p3720_3 (m.d 0 3) (by simp) with h3768 | h3768
                                      · rcases p3720_3 (m.d 0 4) (by simp) with h3769 | h3769
                                        · linarith only [h3701, h3769, hlam]
                                        · rcases p3720_3 (m.d 0 5) (by simp) with h3771 | h3771
                                          · linarith only [h3702, h3771, hlam]
                                          · rcases h2bigk with h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c | h3773c
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3477, h4, hc12, hc23, hlam, hphi, p3720_1, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h4, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3477, h3714, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3720_1, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3477, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h0, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3705, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h0, h3477, h3714, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3720_1, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3708, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              rcases p3773_3 (m.d 0 2) (by simp) with h3784 | h3784
                                              · linarith only [h3784, hlam, p3773_0]
                                              · rcases p3773_3 (m.d 1 2) (by simp) with h3786 | h3786
                                                · linarith only [h3705, h3786, hlam]
                                                · rcases p3773_3 (m.d 2 3) (by simp) with h3788 | h3788
                                                  · rcases p3773_3 (m.d 2 4) (by simp) with h3789 | h3789
                                                    · linarith only [h3714, h3789, hlam]
                                                    · rcases p3773_3 (m.d 2 5) (by simp) with h3791 | h3791
                                                      · linarith only [h3715, h3791, hlam]
                                                      · linarith only [h3477, h3791, hlam]
                                                  · linarith only [h3788, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              rcases p3773_3 (m.d 0 2) (by simp) with h3795 | h3795
                                              · linarith only [h3795, h4, hlam]
                                              · linarith only [h0, h3795, hlam]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3476, h3477, h4, hlam, p3720_1, p3773_2]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3477, hc02, hc23, hlam, hphi, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3476, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3707, hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3714, hlam, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [hlam, p3773_0]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3716, hlam, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h0, h3707, h3714, h3716, hc34, hc45, hlam, hphi, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3707, h3714, h3716, hc34, hc45, hlam, hphi, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [h3715, hlam, p3773_1]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              rcases p3773_3 (m.d 0 2) (by simp) with h3809 | h3809
                                              · linarith only [h3477, h3809, hlam]
                                              · linarith only [h3476, h3809, hlam]
                                            · have p3773_0 := h3773c.1
                                              have p3773_1 := h3773c.2.1
                                              have p3773_2 := h3773c.2.2.1
                                              have p3773_3 := h3773c.2.2.2
                                              linarith only [hlam, p3773_0]
                                      · linarith only [h3702, h3768, hlam]
                                  · linarith only [h3, h3765, hlam]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h2, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h3476, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h3701, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h3703, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h3, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h0, h3477, h3707, h3714, h3716, hc34, hc45, hlam, hphi, p3720_1]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [h3702, hlam, p3720_0]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  rcases p3720_3 (m.d 0 1) (by simp) with h3823 | h3823
                                  · rcases p3720_3 (m.d 0 2) (by simp) with h3824 | h3824
                                    · linarith only [h3477, h3824, hlam]
                                    · linarith only [h3476, h3824, hlam]
                                  · linarith only [h2, h3823, hlam]
                                · have p3720_0 := h3720c.1
                                  have p3720_1 := h3720c.2.1
                                  have p3720_2 := h3720c.2.2.1
                                  have p3720_3 := h3720c.2.2.2
                                  linarith only [hlam, p3720_0]
                          · linarith only [h1, h3711, h3715, h4, hlam]
                        · linarith only [h3701, h3714, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3831 | h3831
                      · linarith only [h2, h3476, h3477, h3703, h3831, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3833 | h3833
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3834 | h3834
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3835 | h3835
                            · linarith only [h3702, h3703, h3705, h3707, h3711, h3835, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3837 | h3837
                              · linarith only [h3476, h3477, h3833, h3835, h3837, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · rcases h0bigk with h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c | h3839c
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  rcases p3839_3 (m.d 0 1) (by simp) with h3841 | h3841
                                  · rcases p3839_3 (m.d 0 2) (by simp) with h3842 | h3842
                                    · linarith only [h0, h3842, hlam]
                                    · rcases p3839_3 (m.d 0 3) (by simp) with h3844 | h3844
                                      · linarith only [h1, h3844, hlam]
                                      · linarith only [h3844, h4, hlam]
                                  · linarith only [h0, h3841, hlam]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3702, h3705, h3707, h3711, h3833, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3839_1]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  rcases p3839_3 (m.d 0 1) (by simp) with h3849 | h3849
                                  · rcases p3839_3 (m.d 0 2) (by simp) with h3850 | h3850
                                    · linarith only [h0, h3850, hlam]
                                    · linarith only [h3476, h3850, hlam]
                                  · linarith only [h2, h3849, hlam]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3702, h3705, h3707, h3711, h3833, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3839_1]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h0, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h4, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3477, h3835, hc04, hc45, hlam, hphi, p3839_1]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3477, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h1, hlam, p3839_1]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  rcases p3839_3 (m.d 0 1) (by simp) with h3861 | h3861
                                  · rcases p3839_3 (m.d 0 2) (by simp) with h3862 | h3862
                                    · linarith only [h3862, h4, hlam]
                                    · rcases p3839_3 (m.d 0 3) (by simp) with h3864 | h3864
                                      · rcases p3839_3 (m.d 0 4) (by simp) with h3865 | h3865
                                        · linarith only [h3701, h3865, hlam]
                                        · rcases p3839_3 (m.d 0 5) (by simp) with h3867 | h3867
                                          · linarith only [h3702, h3867, hlam]
                                          · linarith only [h3477, h3867, hlam]
                                      · linarith only [h3864, h4, hlam]
                                  · linarith only [h0, h3861, hlam]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  rcases p3839_3 (m.d 0 1) (by simp) with h3873 | h3873
                                  · rcases p3839_3 (m.d 0 2) (by simp) with h3874 | h3874
                                    · linarith only [h3874, h4, hlam]
                                    · linarith only [h3476, h3874, hlam]
                                  · linarith only [h2, h3873, hlam]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3702, h3705, h3707, h3711, h3833, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3839_1]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h2, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3476, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3701, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3703, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h0, h3477, h3707, h3833, h3835, hc34, hc45, hlam, hphi, p3839_1]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [h3702, hlam, p3839_0]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  rcases p3839_3 (m.d 0 1) (by simp) with h3887 | h3887
                                  · rcases p3839_3 (m.d 0 2) (by simp) with h3888 | h3888
                                    · linarith only [h3477, h3888, hlam]
                                    · linarith only [h3476, h3888, hlam]
                                  · linarith only [h2, h3887, hlam]
                                · have p3839_0 := h3839c.1
                                  have p3839_1 := h3839c.2.1
                                  have p3839_2 := h3839c.2.2.1
                                  have p3839_3 := h3839c.2.2.2
                                  linarith only [hlam, p3839_0]
                          · linarith only [h3702, h3834, h4, hlam]
                        · linarith only [h3702, h3705, h3707, h3711, h3833, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h3701, h3703, h3705, h3707, h3710, hc24, hc45, hlam, hphi]
              · linarith only [h3476, h3477, h3707, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3897 | h3897
          · linarith only [h3476, h3477, h3897, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3899 | h3899
            · linarith only [h0, h3899, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3901 | h3901
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3902 | h3902
                · linarith only [h0, h3477, h3902, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3904 | h3904
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3905 | h3905
                    · linarith only [h1, h3702, h3905, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3907 | h3907
                      · linarith only [h2, h3897, h3907, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3909 | h3909
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3910 | h3910
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3911 | h3911
                            · linarith only [h3476, h3702, h3897, h3911, h4, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3913 | h3913
                              · linarith only [h0, h3702, h3901, h3909, h3910, h3911, h3913, h4, hlam]
                              · rcases h0bigk with h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  rcases p3915_3 (m.d 0 1) (by simp) with h3917 | h3917
                                  · rcases p3915_3 (m.d 0 2) (by simp) with h3918 | h3918
                                    · linarith only [h0, h3918, hlam]
                                    · rcases p3915_3 (m.d 0 3) (by simp) with h3920 | h3920
                                      · linarith only [h1, h3920, hlam]
                                      · linarith only [h3920, h4, hlam]
                                  · linarith only [h0, h3917, hlam]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  rcases p3915_3 (m.d 0 1) (by simp) with h3924 | h3924
                                  · rcases p3915_3 (m.d 0 2) (by simp) with h3925 | h3925
                                    · linarith only [h0, h3925, hlam]
                                    · rcases p3915_3 (m.d 0 3) (by simp) with h3927 | h3927
                                      · linarith only [h1, h3927, hlam]
                                      · rcases p3915_3 (m.d 0 4) (by simp) with h3929 | h3929
                                        · linarith only [h2, h3929, hlam]
                                        · rcases p3915_3 (m.d 0 5) (by simp) with h3931 | h3931
                                          · linarith only [h3, h3931, hlam]
                                          · linarith only [h3702, h3931, hlam]
                                  · linarith only [h1, h3924, hlam]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  rcases p3915_3 (m.d 0 1) (by simp) with h3935 | h3935
                                  · rcases p3915_3 (m.d 0 2) (by simp) with h3936 | h3936
                                    · linarith only [h0, h3936, hlam]
                                    · linarith only [h3476, h3936, hlam]
                                  · linarith only [h2, h3935, hlam]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  rcases p3915_3 (m.d 0 1) (by simp) with h3940 | h3940
                                  · rcases p3915_3 (m.d 0 2) (by simp) with h3941 | h3941
                                    · linarith only [h0, h3941, hlam]
                                    · rcases p3915_3 (m.d 0 3) (by simp) with h3943 | h3943
                                      · linarith only [h1, h3943, hlam]
                                      · rcases p3915_3 (m.d 0 4) (by simp) with h3945 | h3945
                                        · linarith only [h2, h3945, hlam]
                                        · rcases p3915_3 (m.d 0 5) (by simp) with h3947 | h3947
                                          · linarith only [h3, h3947, hlam]
                                          · rcases h2bigk with h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c | h3949c
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3702, h3901, h3909, h3910, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h4, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3702, h3909, h3910, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3477, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h0, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3899, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h0, h3702, h3909, h3910, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3902, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              rcases p3949_3 (m.d 0 2) (by simp) with h3960 | h3960
                                              · linarith only [h3960, hlam, p3949_0]
                                              · rcases p3949_3 (m.d 1 2) (by simp) with h3962 | h3962
                                                · linarith only [h3899, h3962, hlam]
                                                · rcases p3949_3 (m.d 2 3) (by simp) with h3964 | h3964
                                                  · rcases p3949_3 (m.d 2 4) (by simp) with h3965 | h3965
                                                    · linarith only [h3909, h3965, hlam]
                                                    · rcases p3949_3 (m.d 2 5) (by simp) with h3967 | h3967
                                                      · linarith only [h3910, h3967, hlam]
                                                      · linarith only [h3477, h3967, hlam]
                                                  · linarith only [h3964, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              rcases p3949_3 (m.d 0 2) (by simp) with h3971 | h3971
                                              · linarith only [h3971, h4, hlam]
                                              · linarith only [h0, h3971, hlam]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3476, h3702, h3910, h4, hlam, p3949_2]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3702, h3910, h4, hc02, hc23, hlam, hphi, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3476, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3901, hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3909, hlam, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [hlam, p3949_0]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3911, hlam, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h0, h3901, h3911, hc24, hc45, hlam, hphi, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3901, h3911, hc24, hc45, hlam, hphi, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [h3910, hlam, p3949_1]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              rcases p3949_3 (m.d 0 2) (by simp) with h3985 | h3985
                                              · linarith only [h3477, h3985, hlam]
                                              · linarith only [h3476, h3985, hlam]
                                            · have p3949_0 := h3949c.1
                                              have p3949_1 := h3949c.2.1
                                              have p3949_2 := h3949c.2.2.1
                                              have p3949_3 := h3949c.2.2.2
                                              linarith only [hlam, p3949_0]
                                  · linarith only [h3, h3940, hlam]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h0, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h4, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h2, h3477, h3901, h3909, h3911, hc34, hc45, hlam, hphi, p3915_1]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h3477, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h1, hlam, p3915_1]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h3702, hc02, hc35, hlam, hphi, ht23, p3915_1]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h2, h3702, h3901, h3909, h3910, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3915_1]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h3702, hlam, p3915_1]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h2, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h3476, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h3701, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h3897, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h3, hlam, p3915_0]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h0, h3477, h3901, h3909, h3911, hc34, hc45, hlam, hphi, p3915_1]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [h0, h3702, h3901, h3909, h3910, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3915_1]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  rcases p3915_3 (m.d 0 1) (by simp) with h4008 | h4008
                                  · rcases p3915_3 (m.d 0 2) (by simp) with h4009 | h4009
                                    · linarith only [h3477, h4009, hlam]
                                    · linarith only [h3476, h4009, hlam]
                                  · linarith only [h2, h4008, hlam]
                                · have p3915_0 := h3915c.1
                                  have p3915_1 := h3915c.2.1
                                  have p3915_2 := h3915c.2.2.1
                                  have p3915_3 := h3915c.2.2.2
                                  linarith only [hlam, p3915_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4014 | h4014
                            · linarith only [h0, h3901, h4014, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4016 | h4016
                              · linarith only [h0, h3901, h3909, h3910, h4, h4014, h4016, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                              · linarith only [h0, h3901, h3909, h3910, h4, h4016, hc34, hc45, hlam, hphi]
                        · linarith only [h0, h3701, h3901, h3909, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h3701, h3702, h3899, h3901, h3904, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h3476, h3901, h4, hc12, hc23, hlam, hphi]
      · linarith only [h3476, h3701, h4, hlam]
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s8 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h3476

set_option maxHeartbeats 13294000 in
set_option maxHeartbeats 13294000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s3 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s4 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s7 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 13542000 in
set_option maxHeartbeats 13542000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s2 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6651 | h6651
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6652 | h6652
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6653 | h6653
        · linarith only [h0, h3, h6653, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6655 | h6655
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6656 | h6656
            · linarith only [h0, h3, h6651, h6656, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6658 | h6658
              · linarith only [h0, h3, h6651, h6655, h6658, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6660 | h6660
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6661 | h6661
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6662 | h6662
                    · linarith only [h0, h6653, h6662, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6664 | h6664
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6665 | h6665
                        · linarith only [h0, h3, h6660, h6662, h6665, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h3, h6660, h6665, hc23, hc35, hlam, hphi]
                      · linarith only [h6655, h6656, h6664, hc13, hc35, hlam, hphi]
                  · linarith only [h6652, h6653, h6661, hc12, hc25, hlam, hphi]
                · linarith only [h6651, h6653, h6660, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6671 | h6671
            · linarith only [h1, h3, h6671, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6673 | h6673
              · linarith only [h0, h3, h6652, h6673, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6675 | h6675
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6676 | h6676
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6677 | h6677
                    · linarith only [h0, h6653, h6677, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6679 | h6679
                      · linarith only [h1, h6655, h6679, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6681 | h6681
                        · linarith only [h0, h3, h6676, h6677, h6679, h6681, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h0, h3, h6675, h6681, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h6652, h6675, h6676, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h6651, h6653, h6675, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6686 | h6686
        · linarith only [h0, h3, h6686, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6688 | h6688
          · linarith only [h6651, h6652, h6688, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6690 | h6690
            · linarith only [h2, h3, h6651, h6652, h6690, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6692 | h6692
              · linarith only [h2, h3, h6692, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6694 | h6694
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6695 | h6695
                  · linarith only [h0, h6652, h6695, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6697 | h6697
                    · linarith only [h0, h3, h6697, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6699 | h6699
                      · linarith only [h1, h3, h6688, h6697, h6699, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6701 | h6701
                        · linarith only [h1, h3, h6697, h6701, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · linarith only [h2, h3, h6694, h6695, h6701, hc23, hc35, hlam, hphi]
                · linarith only [h6651, h6652, h6694, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6705 | h6705
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6706 | h6706
        · linarith only [h1, h3, h6651, h6706, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6708 | h6708
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6709 | h6709
            · linarith only [h1, h3, h6709, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6711 | h6711
              · linarith only [h1, h3, h6651, h6705, h6711, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6713 | h6713
                · linarith only [h0, h3, h6651, h6713, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6715 | h6715
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6716 | h6716
                    · linarith only [h0, h3, h6706, h6716, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6718 | h6718
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6719 | h6719
                        · linarith only [h1, h3, h6709, h6719, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6721 | h6721
                          · linarith only [h2, h3, h6711, h6721, hlam]
                          · linarith only [h1, h3, h6713, h6715, h6721, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h6708, h6713, h6715, h6718, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h6651, h6705, h6715, hc12, hc23, hlam, hphi]
          · linarith only [h6651, h6705, h6708, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6727 | h6727
        · linarith only [h0, h3, h6727, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6729 | h6729
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6730 | h6730
            · linarith only [h1, h3, h6730, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6732 | h6732
              · linarith only [h1, h3, h6729, h6732, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6734 | h6734
                · linarith only [h0, h6651, h6734, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6736 | h6736
                  · linarith only [h0, h6705, h6736, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6738 | h6738
                    · linarith only [h1, h3, h6727, h6734, h6738, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6740 | h6740
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6741 | h6741
                        · linarith only [h1, h3, h6730, h6738, h6741, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6743 | h6743
                          · linarith only [h1, h3, h6732, h6740, h6743, hlam]
                          · linarith only [h1, h3, h6740, h6743, hc34, hc45, hlam, hphi]
                      · linarith only [h6729, h6730, h6740, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6747 | h6747
            · linarith only [h1, h3, h6747, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6749 | h6749
              · linarith only [h2, h3, h6749, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6751 | h6751
                · linarith only [h0, h6651, h6751, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6753 | h6753
                  · linarith only [h0, h6705, h6753, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6755 | h6755
                    · linarith only [h1, h3, h6751, h6755, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6757 | h6757
                      · linarith only [h1, h3, h6651, h6729, h6755, h6757, hc02, hc25, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6759 | h6759
                        · linarith only [h2, h3, h6747, h6755, h6757, h6759, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6761 | h6761
                          · linarith only [h2, h3, h6759, h6761, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6763 | h6763
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6764 | h6764
                              · linarith only [h0, h3, h6759, h6764, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h6651, h6729, h6763, h6764, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6767 | h6767
                              · linarith only [h0, h6651, h6747, h6763, h6767, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6769 | h6769
                                · linarith only [h2, h3, h6751, h6757, h6761, h6769, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6771 | h6771
                                  · linarith only [h0, h6651, h6763, h6769, h6771, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h6651, h6763, h6771, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 13994000 in
set_option maxHeartbeats 13994000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s2 m hb0 hb2 hb3 hb5 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h6774 | h6774
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6775 | h6775
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6776 | h6776
        · linarith only [h0, h2, h6776, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6778 | h6778
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6779 | h6779
            · linarith only [h1, h2, h6779, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6781 | h6781
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6782 | h6782
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6783 | h6783
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6784 | h6784
                    · linarith only [h0, h6775, h6776, h6781, h6784, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6786 | h6786
                      · linarith only [h0, h2, h6784, h6786, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h2, h6778, h6783, h6784, h6786, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h6775, h6776, h6783, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h6781, h6782, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6791 | h6791
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6792 | h6792
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6793 | h6793
                    · linarith only [h0, h6776, h6778, h6793, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6795 | h6795
                      · linarith only [h0, h2, h6793, h6795, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h2, h6778, h6792, h6793, h6795, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h6775, h6776, h6792, hc12, hc24, hlam, hphi]
                · linarith only [h2, h6774, h6791, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6800 | h6800
            · linarith only [h1, h2, h6800, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6802 | h6802
              · linarith only [h6775, h6778, h6802, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6804 | h6804
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6805 | h6805
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6806 | h6806
                    · linarith only [h0, h6776, h6806, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6808 | h6808
                      · linarith only [h0, h2, h6778, h6806, h6808, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6810 | h6810
                        · linarith only [h1, h2, h6800, h6804, h6806, h6810, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h2, h6774, h6805, h6808, h6810, hc23, hc34, hlam, hphi]
                  · linarith only [h6775, h6778, h6805, hc12, hc25, hlam, hphi]
                · linarith only [h2, h6774, h6804, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6815 | h6815
        · linarith only [h0, h2, h6815, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6817 | h6817
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6818 | h6818
            · linarith only [h1, h2, h6818, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6820 | h6820
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6821 | h6821
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6822 | h6822
                  · linarith only [h6775, h6817, h6822, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6824 | h6824
                    · linarith only [h1, h6815, h6817, h6822, h6824, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6826 | h6826
                      · linarith only [h1, h2, h6822, h6824, h6826, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h6775, h6817, h6826, hc12, hc23, hlam, hphi]
                · linarith only [h1, h2, h6775, h6817, h6821, hlam]
              · linarith only [h6775, h6817, h6820, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6831 | h6831
            · linarith only [h1, h2, h6831, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6833 | h6833
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6834 | h6834
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6835 | h6835
                  · linarith only [h0, h6775, h6835, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6837 | h6837
                    · linarith only [h0, h6815, h6837, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6839 | h6839
                      · linarith only [h0, h6817, h6839, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6841 | h6841
                        · linarith only [h1, h2, h6831, h6841, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6843 | h6843
                          · linarith only [h1, h2, h6841, h6843, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1, h2, h6833, h6841, h6843, hc13, hc34, hlam, hphi]
                · linarith only [h2, h6774, h6834, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6847 | h6847
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6848 | h6848
                  · linarith only [h0, h6775, h6848, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6850 | h6850
                    · linarith only [h0, h6815, h6850, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6852 | h6852
                      · linarith only [h0, h6817, h6852, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6854 | h6854
                        · linarith only [h1, h2, h6775, h6831, h6850, h6854, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6856 | h6856
                          · linarith only [h1, h6833, h6856, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6858 | h6858
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6859 | h6859
                              · linarith only [h0, h2, h6854, h6859, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6861 | h6861
                                · linarith only [h0, h6775, h6833, h6859, h6861, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6863 | h6863
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6864 | h6864
                                    · rcases h0bigk with h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c | h6865c
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h0, h2, h6850, h6859, hc12, hc34, hlam, hphi, ht23, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h0, h2, h6775, h6850, h6859, hc12, hc34, hlam, hphi, ht23, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h2, hlam, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h2, h6774, h6858, hc14, hlam, hphi, ht01, ht0b, ht5b, p6865_1, u5ehi4]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h0, hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h6775, hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h6815, hlam, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h6817, hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h1, hlam, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h0, h6775, h6861, h6864, hc12, hc34, hlam, hphi, ht23, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h6831, hlam, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h6833, hlam, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h2, h6774, h6858, hc14, hlam, hphi, ht01, ht0b, ht5b, p6865_1, u5ehi4]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        rcases p6865_3 (m.d 0 1) (by simp) with h6882 | h6882
                                        · linarith only [h2, h6882, hlam]
                                        · linarith only [h0, h6882, hlam]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        rcases p6865_3 (m.d 0 1) (by simp) with h6885 | h6885
                                        · linarith only [h2, h6885, hlam]
                                        · linarith only [h1, h6885, hlam]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        rcases p6865_3 (m.d 0 1) (by simp) with h6889 | h6889
                                        · linarith only [h2, h6889, hlam]
                                        · linarith only [h6774, h6889, hlam]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h6774, hlam, p6865_0]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h0, h2, h6774, h6850, h6859, hc12, hc34, hlam, hphi, ht23, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h2, h6774, h6850, h6859, hc03, hc34, hlam, hphi, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [h6847, hlam, p6865_1]
                                      · have p6865_0 := h6865c.1
                                        have p6865_1 := h6865c.2.1
                                        have p6865_2 := h6865c.2.2.1
                                        have p6865_3 := h6865c.2.2.2
                                        linarith only [hlam, p6865_0]
                                    · linarith only [h2, h6774, h6850, h6858, h6859, h6864, hlam]
                                  · linarith only [h2, h6774, h6850, h6858, h6863, hlam]
                            · linarith only [h2, h6774, h6858, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                · linarith only [h2, h6774, h6847, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h6901 | h6901
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6902 | h6902
        · linarith only [h0, h2, h6902, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6904 | h6904
          · linarith only [h0, h6774, h6904, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6906 | h6906
            · linarith only [h1, h2, h6906, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6908 | h6908
              · linarith only [h0, h6774, h6901, h6908, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6910 | h6910
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6911 | h6911
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6912 | h6912
                    · linarith only [h0, h6774, h6902, h6912, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6914 | h6914
                      · linarith only [h0, h6774, h6904, h6914, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6916 | h6916
                        · linarith only [h0, h6774, h6906, h6910, h6911, h6916, hlam]
                        · linarith only [h0, h2, h6911, h6916, hc23, hc34, hlam, hphi]
                  · linarith only [h6901, h6902, h6911, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6920 | h6920
                  · linarith only [h0, h2, h6910, h6920, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h6901, h6910, h6920, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6923 | h6923
        · linarith only [h1, h2, h6901, h6923, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h6925 | h6925
          · linarith only [h1, h6774, h6901, h6925, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h6927 | h6927
            · linarith only [h1, h2, h6927, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6929 | h6929
              · linarith only [h1, h6774, h6929, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6931 | h6931
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6932 | h6932
                  · linarith only [h0, h2, h6901, h6932, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6934 | h6934
                    · linarith only [h0, h6923, h6934, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6936 | h6936
                      · linarith only [h0, h2, h6925, h6934, h6936, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6938 | h6938
                        · linarith only [h1, h2, h6927, h6931, h6934, h6938, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6940 | h6940
                          · linarith only [h1, h2, h6929, h6938, h6940, hc03, hc34, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6942 | h6942
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6943 | h6943
                              · linarith only [h1, h6774, h6932, h6938, h6942, h6943, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6945 | h6945
                                · linarith only [h1, h6774, h6932, h6940, h6943, h6945, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6947 | h6947
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6948 | h6948
                                    · rcases h0bigk with h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c | h6949c
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [hlam, p6949_0]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h0, h6774, h6934, h6942, hc12, hc24, hlam, hphi, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h1, h6774, h6932, h6934, h6942, hc12, hc24, hlam, hphi, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h2, hlam, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h6774, hlam, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h0, hlam, p6949_0]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [hlam, p6949_0]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h6901, hlam, p6949_0]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h6923, hlam, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h6925, hlam, p6949_0]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h1, hlam, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h0, h1, h6774, h6934, h6942, hc12, hc24, hlam, hphi, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [hlam, p6949_0]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h6927, hlam, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h6929, hlam, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h0, h2, h6934, hc12, hc24, hlam, hphi, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        rcases p6949_3 (m.d 0 1) (by simp) with h6966 | h6966
                                        · linarith only [h2, h6966, hlam]
                                        · linarith only [h0, h6966, hlam]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        rcases p6949_3 (m.d 0 1) (by simp) with h6969 | h6969
                                        · linarith only [h2, h6969, hlam]
                                        · linarith only [h1, h6969, hlam]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [hlam, p6949_0]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h1, h2, h6774, h6932, h6934, h6943, hc12, hc34, hlam, hphi, ht23, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h1, h6774, h6932, h6934, h6942, h6943, hc12, hc34, hlam, hphi, ht23, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        rcases p6949_3 (m.d 0 1) (by simp) with h6975 | h6975
                                        · linarith only [h6774, h6975, hlam]
                                        · linarith only [h0, h6975, hlam]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        rcases p6949_3 (m.d 0 1) (by simp) with h6978 | h6978
                                        · linarith only [h6774, h6978, hlam]
                                        · linarith only [h1, h6978, hlam]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [h6931, hlam, p6949_1]
                                      · have p6949_0 := h6949c.1
                                        have p6949_1 := h6949c.2.1
                                        have p6949_2 := h6949c.2.2.1
                                        have p6949_3 := h6949c.2.2.2
                                        linarith only [hlam, p6949_0]
                                    · linarith only [h1, h2, h6932, h6934, h6943, h6948, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h2, h6931, h6934, h6947, hlam]
                            · linarith only [h2, h6931, h6942, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6986 | h6986
                  · linarith only [h0, h2, h6931, h6986, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6988 | h6988
                    · linarith only [h1, h2, h6931, h6986, h6988, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6990 | h6990
                      · linarith only [h1, h2, h6931, h6986, h6990, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6992 | h6992
                        · linarith only [h1, h2, h6931, h6992, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6994 | h6994
                          · linarith only [h1, h2, h6931, h6994, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6996 | h6996
                            · linarith only [h1, h2, h6931, h6986, h6988, h6996, hc12, hc24, hlam, hphi]
                            · linarith only [h1, h2, h6986, h6996, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
