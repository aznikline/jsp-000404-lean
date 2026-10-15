import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S4
import Jsp000404.R1LeavesN7_4S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8294000 in
set_option maxHeartbeats 8294000 in
theorem r1l7_11_23_L_I_H_I_s7_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2917 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h3518 | h3518
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3519 | h3519
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3520 | h3520
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3521 | h3521
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3522 | h3522
          · linarith only [h2, h3522, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3524 | h3524
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3525 | h3525
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3526 | h3526
                · linarith only [h2917, h3518, h3526, h8, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3528 | h3528
                  · linarith only [h2, h3518, h3524, h3528, h8, hlam]
                  · rcases h1bigk with h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c | h3530c
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      rcases p3530_3 (m.d 0 1) (by simp) with h3532 | h3532
                      · rcases p3530_3 (m.d 1 2) (by simp) with h3533 | h3533
                        · linarith only [h3533, hlam, p3530_0]
                        · rcases p3530_3 (m.d 1 3) (by simp) with h3535 | h3535
                          · linarith only [h1, h3535, hlam]
                          · linarith only [h2917, h3535, hlam]
                      · linarith only [h3532, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      rcases p3530_3 (m.d 0 1) (by simp) with h3539 | h3539
                      · rcases p3530_3 (m.d 1 2) (by simp) with h3540 | h3540
                        · linarith only [h0, h3540, hlam]
                        · rcases p3530_3 (m.d 1 3) (by simp) with h3542 | h3542
                          · linarith only [h3542, hlam, p3530_0]
                          · rcases p3530_3 (m.d 1 4) (by simp) with h3544 | h3544
                            · linarith only [h2, h3544, hlam]
                            · rcases p3530_3 (m.d 1 5) (by simp) with h3546 | h3546
                              · linarith only [h3, h3546, hlam]
                              · rcases h3bigk with h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c | h3548c
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h0, h4, hlam, p3530_2, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h0, h2917, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  rcases p3548_3 (m.d 0 3) (by simp) with h3552 | h3552
                                  · rcases p3548_3 (m.d 1 3) (by simp) with h3553 | h3553
                                    · linarith only [h1, h3553, hlam]
                                    · linarith only [h3520, h3553, hlam]
                                  · linarith only [h3552, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  rcases p3548_3 (m.d 0 3) (by simp) with h3557 | h3557
                                  · rcases p3548_3 (m.d 1 3) (by simp) with h3558 | h3558
                                    · linarith only [h1, h3558, hlam]
                                    · linarith only [h3521, h3558, hlam]
                                  · linarith only [h3557, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h1, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h2917, hlam, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3530_1, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p3530_1, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h4, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h0, h4, hlam, p3530_2, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h6, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h3520, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h3524, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h3528, hlam, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h7, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h3521, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h3525, hlam, p3548_0]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3548_1]
                                · have p3548_0 := h3548c.1
                                  have p3548_1 := h3548c.2.1
                                  have p3548_2 := h3548c.2.2.1
                                  have p3548_3 := h3548c.2.2.2
                                  linarith only [hlam, p3548_0]
                      · linarith only [h3539, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      rcases p3530_3 (m.d 0 1) (by simp) with h3583 | h3583
                      · rcases p3530_3 (m.d 1 2) (by simp) with h3584 | h3584
                        · linarith only [h0, h3584, hlam]
                        · linarith only [h3518, h3584, hlam]
                      · linarith only [h3583, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      rcases p3530_3 (m.d 0 1) (by simp) with h3588 | h3588
                      · rcases p3530_3 (m.d 1 2) (by simp) with h3589 | h3589
                        · linarith only [h0, h3589, hlam]
                        · linarith only [h3519, h3589, hlam]
                      · linarith only [h3588, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h0, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h2917, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h0, h2917, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3530_1]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h0, h2917, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3530_1]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h1, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h0, h2917, h3519, h4, hc01, hc25, hlam, hphi, ht0b, ht5b, p3530_1]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      rcases p3530_3 (m.d 0 1) (by simp) with h3601 | h3601
                      · rcases p3530_3 (m.d 1 2) (by simp) with h3602 | h3602
                        · linarith only [h2917, h3602, hlam]
                        · linarith only [h3518, h3602, hlam]
                      · linarith only [h2, h3601, hlam]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      rcases p3530_3 (m.d 0 1) (by simp) with h3606 | h3606
                      · rcases p3530_3 (m.d 1 2) (by simp) with h3607 | h3607
                        · linarith only [h2917, h3607, hlam]
                        · linarith only [h3519, h3607, hlam]
                      · linarith only [h3, h3606, hlam]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h2, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h3518, hlam, p3530_1]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h3520, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h3522, hlam, p3530_1]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h3, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h3519, hlam, p3530_1]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h3521, hlam, p3530_0]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [h0, h2917, h3518, h3519, h3524, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3530_1]
                    · have p3530_0 := h3530c.1
                      have p3530_1 := h3530c.2.1
                      have p3530_2 := h3530c.2.2.1
                      have p3530_3 := h3530c.2.2.2
                      linarith only [hlam, p3530_0]
              · linarith only [h0, h2917, h3518, h3524, h3525, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h2917, h3518, h3524, h6, h8, hc24, hc45, hlam, hphi]
        · linarith only [h2917, h3519, h3521, hlam]
      · linarith only [h2917, h3518, h3520, h6, h8, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3625 | h3625
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3626 | h3626
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3627 | h3627
          · linarith only [h2, h3627, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3629 | h3629
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3630 | h3630
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3631 | h3631
                · linarith only [h2, h3518, h3519, h3631, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3633 | h3633
                  · linarith only [h3518, h3519, h3629, h3631, h3633, hlam]
                  · rcases h1bigk with h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 1) (by simp) with h3637 | h3637
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3638 | h3638
                        · linarith only [h3638, hlam, p3635_0]
                        · rcases p3635_3 (m.d 1 3) (by simp) with h3640 | h3640
                          · linarith only [h1, h3640, hlam]
                          · linarith only [h2917, h3640, hlam]
                      · linarith only [h3637, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 1) (by simp) with h3644 | h3644
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3645 | h3645
                        · linarith only [h0, h3645, hlam]
                        · rcases p3635_3 (m.d 1 3) (by simp) with h3647 | h3647
                          · linarith only [h3647, hlam, p3635_0]
                          · rcases p3635_3 (m.d 1 4) (by simp) with h3649 | h3649
                            · linarith only [h2, h3649, hlam]
                            · rcases p3635_3 (m.d 1 5) (by simp) with h3651 | h3651
                              · linarith only [h3, h3651, hlam]
                              · rcases h3bigk with h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c | h3653c
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h0, h3626, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h0, h2917, h3518, h3629, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  rcases p3653_3 (m.d 0 3) (by simp) with h3657 | h3657
                                  · rcases p3653_3 (m.d 1 3) (by simp) with h3658 | h3658
                                    · linarith only [h1, h3658, hlam]
                                    · linarith only [h3625, h3658, hlam]
                                  · linarith only [h3657, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  rcases p3653_3 (m.d 0 3) (by simp) with h3662 | h3662
                                  · rcases p3653_3 (m.d 1 3) (by simp) with h3663 | h3663
                                    · linarith only [h1, h3663, hlam]
                                    · linarith only [h3626, h3663, hlam]
                                  · linarith only [h3662, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h1, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h2917, hlam, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3635_1, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h3633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3635_1, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h4, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h0, h4, hlam, p3635_2, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h0, h3633, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h6, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h3625, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h3629, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h3633, hlam, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h7, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h3626, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h3630, hlam, p3653_0]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3653_1]
                                · have p3653_0 := h3653c.1
                                  have p3653_1 := h3653c.2.1
                                  have p3653_2 := h3653c.2.2.1
                                  have p3653_3 := h3653c.2.2.2
                                  linarith only [hlam, p3653_0]
                      · linarith only [h3644, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 1) (by simp) with h3688 | h3688
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3689 | h3689
                        · linarith only [h0, h3689, hlam]
                        · linarith only [h3518, h3689, hlam]
                      · linarith only [h3688, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 1) (by simp) with h3693 | h3693
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3694 | h3694
                        · linarith only [h0, h3694, hlam]
                        · rcases p3635_3 (m.d 1 3) (by simp) with h3696 | h3696
                          · linarith only [h1, h3696, hlam]
                          · linarith only [h3626, h3696, hlam]
                      · linarith only [h3693, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h0, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h2917, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3519, h3631, hc14, hc45, hlam, hphi, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3519, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h1, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h0, h2917, h3518, h3629, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 1) (by simp) with h3708 | h3708
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3709 | h3709
                        · linarith only [h2917, h3709, hlam]
                        · linarith only [h3518, h3709, hlam]
                      · linarith only [h2, h3708, hlam]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h0, h2917, h3518, h3519, h3629, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h2, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3518, hlam, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3625, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3627, hlam, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3, h3518, h3629, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3626, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 1) (by simp) with h3722 | h3722
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3723 | h3723
                        · linarith only [h3519, h3723, hlam]
                        · linarith only [h3518, h3723, hlam]
                      · linarith only [h2, h3722, hlam]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
              · linarith only [h2917, h3626, h3630, hlam]
            · linarith only [h0, h2917, h3518, h3629, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3730 | h3730
          · linarith only [h2, h3730, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3732 | h3732
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3733 | h3733
              · linarith only [h0, h2917, h3518, h3626, h3732, h3733, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h2917, h3518, h3732, h3733, h7, h8, hc34, hc45, hlam, hphi]
            · linarith only [h0, h2917, h3518, h3732, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h2917, h3518, h3625, h6, h8, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3738 | h3738
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3739 | h3739
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3740 | h3740
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3741 | h3741
          · linarith only [h3518, h3738, h3741, h5, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3518, h3738, h3741, hlam]
        · linarith only [h3518, h3738, h3739, h3740, h5, h8, hc34, hc45, hlam, hphi]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3745 | h3745
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3746 | h3746
          · linarith only [h2917, h3738, h3739, h3746, h6, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3518, h3738, h3746, hlam]
        · linarith only [h2917, h3738, h3745, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3750 | h3750
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3751 | h3751
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3752 | h3752
          · linarith only [h2, h3752, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3754 | h3754
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3755 | h3755
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3756 | h3756
                · linarith only [h3756, h5, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3758 | h3758
                  · linarith only [h3518, h3750, h3758, h5, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h1bigk with h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c | h3760c
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3762 | h3762
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3763 | h3763
                        · linarith only [h3763, hlam, p3760_0]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3765 | h3765
                          · linarith only [h1, h3765, hlam]
                          · linarith only [h2917, h3765, hlam]
                      · linarith only [h3762, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3769 | h3769
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3770 | h3770
                        · linarith only [h0, h3770, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3772 | h3772
                          · linarith only [h3772, hlam, p3760_0]
                          · rcases p3760_3 (m.d 1 4) (by simp) with h3774 | h3774
                            · linarith only [h2, h3774, hlam]
                            · rcases p3760_3 (m.d 1 5) (by simp) with h3776 | h3776
                              · linarith only [h3, h3776, hlam]
                              · rcases h3bigk with h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c | h3778c
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h0, h3751, h3758, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h0, h2917, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  rcases p3778_3 (m.d 0 3) (by simp) with h3782 | h3782
                                  · rcases p3778_3 (m.d 1 3) (by simp) with h3783 | h3783
                                    · linarith only [h1, h3783, hlam]
                                    · linarith only [h3750, h3783, hlam]
                                  · linarith only [h3782, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  rcases p3778_3 (m.d 0 3) (by simp) with h3787 | h3787
                                  · rcases p3778_3 (m.d 1 3) (by simp) with h3788 | h3788
                                    · linarith only [h1, h3788, hlam]
                                    · linarith only [h3751, h3788, hlam]
                                  · linarith only [h3787, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h1, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h2917, hlam, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3760_1, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h3758, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3760_1, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h4, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h0, h4, hlam, p3760_2, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h0, h3758, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h6, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h3750, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h3754, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h3758, hlam, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h7, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h3751, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h3755, hlam, p3778_0]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [h3751, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3778_1]
                                · have p3778_0 := h3778c.1
                                  have p3778_1 := h3778c.2.1
                                  have p3778_2 := h3778c.2.2.1
                                  have p3778_3 := h3778c.2.2.2
                                  linarith only [hlam, p3778_0]
                      · linarith only [h3769, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3813 | h3813
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3814 | h3814
                        · linarith only [h0, h3814, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3816 | h3816
                          · linarith only [h1, h3816, hlam]
                          · linarith only [h3750, h3816, hlam]
                      · linarith only [h3813, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3820 | h3820
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3821 | h3821
                        · linarith only [h0, h3821, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3823 | h3823
                          · linarith only [h1, h3823, hlam]
                          · linarith only [h3751, h3823, hlam]
                      · linarith only [h3820, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h0, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h2917, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h3518, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h3738, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h1, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3833 | h3833
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3834 | h3834
                        · linarith only [h2917, h3834, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3836 | h3836
                          · rcases p3760_3 (m.d 1 4) (by simp) with h3837 | h3837
                            · linarith only [h3750, h3837, hlam]
                            · linarith only [h3518, h3837, hlam]
                          · linarith only [h2917, h3836, hlam]
                      · linarith only [h0, h3833, hlam]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3843 | h3843
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3844 | h3844
                        · linarith only [h2917, h3844, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3846 | h3846
                          · rcases p3760_3 (m.d 1 4) (by simp) with h3847 | h3847
                            · linarith only [h3750, h3847, hlam]
                            · rcases p3760_3 (m.d 1 5) (by simp) with h3849 | h3849
                              · linarith only [h3751, h3849, hlam]
                              · linarith only [h3752, h3849, hlam]
                          · linarith only [h3750, h3846, hlam]
                      · linarith only [h2, h3843, hlam]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3854 | h3854
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3855 | h3855
                        · linarith only [h2917, h3855, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3857 | h3857
                          · rcases p3760_3 (m.d 1 4) (by simp) with h3858 | h3858
                            · linarith only [h3750, h3858, hlam]
                            · rcases p3760_3 (m.d 1 5) (by simp) with h3860 | h3860
                              · linarith only [h3751, h3860, hlam]
                              · rcases h3bigk with h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c | h3862c
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h0, h3752, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3760_1, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h0, h2917, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  rcases p3862_3 (m.d 0 3) (by simp) with h3866 | h3866
                                  · rcases p3862_3 (m.d 1 3) (by simp) with h3867 | h3867
                                    · linarith only [h1, h3867, hlam]
                                    · linarith only [h3750, h3867, hlam]
                                  · linarith only [h3866, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  rcases p3862_3 (m.d 0 3) (by simp) with h3871 | h3871
                                  · rcases p3862_3 (m.d 1 3) (by simp) with h3872 | h3872
                                    · linarith only [h1, h3872, hlam]
                                    · linarith only [h3751, h3872, hlam]
                                  · linarith only [h3871, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h1, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h2917, hlam, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h0, h2917, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h4, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h0, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h6, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h3750, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h3754, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h3758, hlam, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h7, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h3751, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h3755, hlam, p3862_0]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3862_1]
                                · have p3862_0 := h3862c.1
                                  have p3862_1 := h3862c.2.1
                                  have p3862_2 := h3862c.2.2.1
                                  have p3862_3 := h3862c.2.2.2
                                  linarith only [hlam, p3862_0]
                          · linarith only [h3751, h3857, hlam]
                      · linarith only [h3, h3854, hlam]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h2, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3760_1]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h3750, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h3752, hlam, p3760_1]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h3, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3904 | h3904
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3905 | h3905
                        · linarith only [h3738, h3905, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3907 | h3907
                          · rcases p3760_3 (m.d 1 4) (by simp) with h3908 | h3908
                            · linarith only [h3752, h3908, hlam]
                            · linarith only [h3518, h3908, hlam]
                          · linarith only [h2917, h3907, hlam]
                      · linarith only [h0, h3904, hlam]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [h3751, hlam, p3760_0]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      rcases p3760_3 (m.d 0 1) (by simp) with h3914 | h3914
                      · rcases p3760_3 (m.d 1 2) (by simp) with h3915 | h3915
                        · linarith only [h3738, h3915, hlam]
                        · rcases p3760_3 (m.d 1 3) (by simp) with h3917 | h3917
                          · rcases p3760_3 (m.d 1 4) (by simp) with h3918 | h3918
                            · linarith only [h3752, h3918, hlam]
                            · rcases p3760_3 (m.d 1 5) (by simp) with h3920 | h3920
                              · rcases h3bigk with h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c | h3921c
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h0, h3751, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h0, h2917, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  rcases p3921_3 (m.d 0 3) (by simp) with h3925 | h3925
                                  · rcases p3921_3 (m.d 1 3) (by simp) with h3926 | h3926
                                    · linarith only [h1, h3926, hlam]
                                    · linarith only [h3750, h3926, hlam]
                                  · linarith only [h3925, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  rcases p3921_3 (m.d 0 3) (by simp) with h3930 | h3930
                                  · rcases p3921_3 (m.d 1 3) (by simp) with h3931 | h3931
                                    · linarith only [h1, h3931, hlam]
                                    · linarith only [h3751, h3931, hlam]
                                  · linarith only [h3930, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h1, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h2917, hlam, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h0, h2917, h3758, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h4, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h0, h3758, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h6, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h3750, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h3754, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h3758, hlam, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h7, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h3751, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h3755, hlam, p3921_0]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3921_1]
                                · have p3921_0 := h3921c.1
                                  have p3921_1 := h3921c.2.1
                                  have p3921_2 := h3921c.2.2.1
                                  have p3921_3 := h3921c.2.2.2
                                  linarith only [hlam, p3921_0]
                              · linarith only [h3752, h3920, hlam]
                          · linarith only [h3750, h3917, hlam]
                      · linarith only [h2, h3914, hlam]
                    · have p3760_0 := h3760c.1
                      have p3760_1 := h3760c.2.1
                      have p3760_2 := h3760c.2.2.1
                      have p3760_3 := h3760c.2.2.2
                      linarith only [hlam, p3760_0]
              · linarith only [h1, h2917, h3751, h3755, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h2917, h3754, h6, h8, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3961 | h3961
          · linarith only [h2, h3961, h8, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3963 | h3963
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3964 | h3964
              · linarith only [h0, h3750, h3751, h3964, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3966 | h3966
                · linarith only [h3963, h3964, h3966, h7, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3968 | h3968
                  · linarith only [h3518, h3750, h3963, h3964, h3968, h7, h8, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h1bigk with h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h0, h3518, h3963, h3964, h4, h7, hlam, p3970_2]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      rcases p3970_3 (m.d 0 1) (by simp) with h3973 | h3973
                      · rcases p3970_3 (m.d 1 2) (by simp) with h3974 | h3974
                        · linarith only [h0, h3974, hlam]
                        · rcases p3970_3 (m.d 1 3) (by simp) with h3976 | h3976
                          · linarith only [h3976, hlam, p3970_0]
                          · rcases p3970_3 (m.d 1 4) (by simp) with h3978 | h3978
                            · linarith only [h2, h3978, hlam]
                            · rcases p3970_3 (m.d 1 5) (by simp) with h3980 | h3980
                              · linarith only [h3, h3980, hlam]
                              · linarith only [h3751, h3980, hlam]
                      · linarith only [h3973, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      rcases p3970_3 (m.d 0 1) (by simp) with h3984 | h3984
                      · rcases p3970_3 (m.d 1 2) (by simp) with h3985 | h3985
                        · linarith only [h0, h3985, hlam]
                        · rcases p3970_3 (m.d 1 3) (by simp) with h3987 | h3987
                          · linarith only [h1, h3987, hlam]
                          · linarith only [h3750, h3987, hlam]
                      · linarith only [h3984, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      rcases p3970_3 (m.d 0 1) (by simp) with h3991 | h3991
                      · rcases p3970_3 (m.d 1 2) (by simp) with h3992 | h3992
                        · linarith only [h0, h3992, hlam]
                        · rcases p3970_3 (m.d 1 3) (by simp) with h3994 | h3994
                          · linarith only [h1, h3994, hlam]
                          · rcases p3970_3 (m.d 1 4) (by simp) with h3996 | h3996
                            · linarith only [h2, h3996, hlam]
                            · rcases p3970_3 (m.d 1 5) (by simp) with h3998 | h3998
                              · linarith only [h3998, hlam, p3970_0]
                              · rcases h3bigk with h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c | h4000c
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h3750, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h0, h3518, h3963, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  rcases p4000_3 (m.d 0 3) (by simp) with h4004 | h4004
                                  · rcases p4000_3 (m.d 1 3) (by simp) with h4005 | h4005
                                    · linarith only [h1, h4005, hlam]
                                    · linarith only [h3750, h4005, hlam]
                                  · linarith only [h4004, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h0, h3518, h3963, h3964, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h1, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h2917, hlam, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h3751, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h4, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h3964, h7, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h0, h3964, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h3964, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h6, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h3750, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h3963, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h3968, hlam, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h7, hlam, p4000_0]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4000_1]
                                · have p4000_0 := h4000c.1
                                  have p4000_1 := h4000c.2.1
                                  have p4000_2 := h4000c.2.2.1
                                  have p4000_3 := h4000c.2.2.2
                                  linarith only [hlam, p4000_0]
                      · linarith only [h3991, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h0, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h2917, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h3518, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h3738, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h1, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h0, h3751, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3970_1]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h0, h3518, h3751, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3970_1]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h3751, hlam, p3970_1]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h2, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p3970_1]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h3750, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h3961, hlam, p3970_1]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h3, hlam, p3970_0]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      rcases p3970_3 (m.d 0 1) (by simp) with h4047 | h4047
                      · rcases p3970_3 (m.d 1 2) (by simp) with h4048 | h4048
                        · linarith only [h3738, h4048, hlam]
                        · rcases p3970_3 (m.d 1 3) (by simp) with h4050 | h4050
                          · linarith only [h3751, h4050, hlam]
                          · linarith only [h2917, h4050, hlam]
                      · linarith only [h0, h4047, hlam]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [h0, h3738, h3750, h3964, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3970_1]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      rcases p3970_3 (m.d 0 1) (by simp) with h4055 | h4055
                      · rcases p3970_3 (m.d 1 2) (by simp) with h4056 | h4056
                        · linarith only [h3738, h4056, hlam]
                        · rcases p3970_3 (m.d 1 3) (by simp) with h4058 | h4058
                          · linarith only [h3751, h4058, hlam]
                          · linarith only [h3750, h4058, hlam]
                      · linarith only [h2, h4055, hlam]
                    · have p3970_0 := h3970c.1
                      have p3970_1 := h3970c.2.1
                      have p3970_2 := h3970c.2.2.1
                      have p3970_3 := h3970c.2.2.2
                      linarith only [hlam, p3970_0]
            · linarith only [h1, h2917, h3750, h3963, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4064 | h4064
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4065 | h4065
          · linarith only [h3750, h4064, h4065, h6, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3750, h4064, h4065, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4068 | h4068
          · linarith only [h2, h3750, h4068, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4070 | h4070
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4071 | h4071
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4072 | h4072
                · linarith only [h4072, h5, h8, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4074 | h4074
                  · linarith only [h4070, h4074, h5, h8, hlam]
                  · rcases h1bigk with h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c | h4076c
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h0, h2917, h3750, h4, h4070, hlam, p4076_2]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h0, h3750, h4, h4070, hlam, p4076_2]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      rcases p4076_3 (m.d 0 1) (by simp) with h4080 | h4080
                      · rcases p4076_3 (m.d 1 2) (by simp) with h4081 | h4081
                        · linarith only [h0, h4081, hlam]
                        · rcases p4076_3 (m.d 1 3) (by simp) with h4083 | h4083
                          · linarith only [h1, h4083, hlam]
                          · rcases p4076_3 (m.d 1 4) (by simp) with h4085 | h4085
                            · linarith only [h4085, hlam, p4076_0]
                            · rcases p4076_3 (m.d 1 5) (by simp) with h4087 | h4087
                              · linarith only [h3, h4087, hlam]
                              · linarith only [h4068, h4087, hlam]
                      · linarith only [h4080, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      rcases p4076_3 (m.d 0 1) (by simp) with h4091 | h4091
                      · rcases p4076_3 (m.d 1 2) (by simp) with h4092 | h4092
                        · linarith only [h0, h4092, hlam]
                        · rcases p4076_3 (m.d 1 3) (by simp) with h4094 | h4094
                          · linarith only [h1, h4094, hlam]
                          · rcases p4076_3 (m.d 1 4) (by simp) with h4096 | h4096
                            · linarith only [h2, h4096, hlam]
                            · rcases p4076_3 (m.d 1 5) (by simp) with h4098 | h4098
                              · linarith only [h4098, hlam, p4076_0]
                              · rcases h3bigk with h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c | h4100c
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  rcases p4100_3 (m.d 0 3) (by simp) with h4102 | h4102
                                  · rcases p4100_3 (m.d 1 3) (by simp) with h4103 | h4103
                                    · linarith only [h1, h4103, hlam]
                                    · rcases p4100_3 (m.d 2 3) (by simp) with h4105 | h4105
                                      · linarith only [h4, h4105, hlam]
                                      · linarith only [h2917, h4105, hlam]
                                  · linarith only [h1, h4102, hlam]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h0, h2917, h3750, h4, h4071, h4074, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h0, h2917, h3750, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h0, h2917, h3750, h4, h4074, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h1, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h2917, hlam, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h3750, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h4064, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h4, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h2917, hc12, hc23, hlam, hphi, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h0, h2917, h3750, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h0, h2917, h3750, h4, h4074, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h6, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h2917, h4070, hc12, hc24, hlam, hphi, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h4070, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h4074, hlam, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h7, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h2917, hc12, hc35, hlam, hphi, ht23, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h4071, hlam, p4100_0]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [h0, h4, h4071, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4100_1]
                                · have p4100_0 := h4100c.1
                                  have p4100_1 := h4100c.2.1
                                  have p4100_2 := h4100c.2.2.1
                                  have p4100_3 := h4100c.2.2.2
                                  linarith only [hlam, p4100_0]
                      · linarith only [h4091, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h0, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h2917, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h3518, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h3738, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h1, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h3750, hc12, hc34, hlam, hphi, ht23, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h3750, hlam, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h4064, hlam, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h2, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h2, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h3518, h5, h8, hc13, hc45, hlam, hphi, ht34, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h4068, hlam, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h3, hlam, p4076_0]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h0, h4, h4064, h4071, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h0, h2917, h4, h4064, h4071, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [h0, h4, h4064, h4071, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4076_1]
                    · have p4076_0 := h4076c.1
                      have p4076_1 := h4076c.2.1
                      have p4076_2 := h4076c.2.2.1
                      have p4076_3 := h4076c.2.2.2
                      linarith only [hlam, p4076_0]
              · linarith only [h2917, h3750, h4070, h4071, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h2917, h4070, h6, h8, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8294000 in
set_option maxHeartbeats 8294000 in
theorem r1l7_11_23_L_I_H_I_s7_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 3 (by decide) (by decide) with h2917 | h2917
  · exact r1l7_11_23_L_I_H_I_s7_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h2917
  · exact r1l7_11_23_L_I_H_I_s7_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h2917

set_option maxHeartbeats 8294000 in
set_option maxHeartbeats 8294000 in
theorem r1l7_11_23_L_I_H_I_s7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_23_L_I_H_I_s7_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8
  · exact r1l7_11_23_L_I_H_I_s7_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8

end R2N4
