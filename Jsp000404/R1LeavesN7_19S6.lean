import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S4
import Jsp000404.R1LeavesN7_19S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8564000 in
set_option maxHeartbeats 8564000 in
theorem r1l7_21_14_H_I_L_I_s3_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h2783 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h3524 | h3524
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3525 | h3525
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3526 | h3526
      · linarith only [h0, h3526, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3528 | h3528
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3529 | h3529
          · linarith only [h1, h2783, h3529, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3531 | h3531
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3532 | h3532
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3533 | h3533
                · linarith only [h2, h2783, h3525, h3526, h3533, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3535 | h3535
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3536 | h3536
                    · rcases h1bigk with h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c | h3537c
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3531, h3536, hc01, hc45, hlam, hphi, ht0b, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3525, h3526, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        rcases p3537_3 (m.d 0 1) (by simp) with h3542 | h3542
                        · rcases p3537_3 (m.d 1 2) (by simp) with h3543 | h3543
                          · linarith only [h0, h3543, hlam]
                          · linarith only [h3528, h3543, hlam]
                        · linarith only [h3542, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h0, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h0, h3531, h3536, hc02, hc45, hlam, hphi, ht0b, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3526, hlam, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h0, h3533, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h1, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3525, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3529, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h1, h3528, hc01, hc25, hlam, hphi, ht0b, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h2, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h2, h3531, h3536, hc01, hc45, hlam, hphi, ht0b, ht5b, p3537_1]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3528, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3531, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [h3532, hlam, p3537_0]
                      · have p3537_0 := h3537c.1
                        have p3537_1 := h3537c.2.1
                        have p3537_2 := h3537c.2.2.1
                        have p3537_3 := h3537c.2.2.2
                        linarith only [hlam, p3537_0]
                    · linarith only [h0, h3525, h3533, h3536, h4, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h3525, h3535, h4, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h2783, h3524, h3525, h3526, h3532, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3570 | h3570
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3571 | h3571
                · linarith only [h0, h2783, h3525, h3571, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3573 | h3573
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3574 | h3574
                    · rcases h1bigk with h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c | h3575c
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3528, hc01, hc25, hlam, hphi, ht0b, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        rcases p3575_3 (m.d 0 1) (by simp) with h3578 | h3578
                        · rcases p3575_3 (m.d 1 2) (by simp) with h3579 | h3579
                          · linarith only [h0, h3579, hlam]
                          · linarith only [h3525, h3579, hlam]
                        · linarith only [h3578, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3525, h3526, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        rcases p3575_3 (m.d 0 1) (by simp) with h3584 | h3584
                        · rcases p3575_3 (m.d 1 2) (by simp) with h3585 | h3585
                          · linarith only [h0, h3585, hlam]
                          · linarith only [h3528, h3585, hlam]
                        · linarith only [h3584, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h0, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h0, h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3526, hlam, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h0, h3571, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h1, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3525, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3529, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3531, hlam, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h2, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h2, h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h2, h3525, h3531, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3528, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3, h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3575_1]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [h3570, hlam, p3575_0]
                      · have p3575_0 := h3575c.1
                        have p3575_1 := h3575c.2.1
                        have p3575_2 := h3575c.2.2.1
                        have p3575_3 := h3575c.2.2.2
                        linarith only [hlam, p3575_0]
                    · linarith only [h3524, h3571, h3574, h4, hlam]
                  · linarith only [h0, h3528, h3570, h3573, h4, hlam]
              · linarith only [h2783, h3524, h3525, h3526, h3570, hc23, hc34, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3612 | h3612
          · linarith only [h1, h2783, h3612, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3614 | h3614
            · linarith only [h3525, h3528, h3614, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3616 | h3616
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3617 | h3617
                · linarith only [h2783, h3525, h3528, h3617, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3619 | h3619
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3620 | h3620
                    · rcases h1bigk with h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c | h3621c
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        rcases p3621_3 (m.d 0 1) (by simp) with h3624 | h3624
                        · rcases p3621_3 (m.d 1 2) (by simp) with h3625 | h3625
                          · linarith only [h0, h3625, hlam]
                          · linarith only [h3525, h3625, hlam]
                        · linarith only [h3624, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3525, h3528, h3616, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3525, h3528, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h0, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h0, h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3526, hlam, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3528, hlam, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h1, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3525, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3612, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3614, hlam, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h2, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h2, h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h2, hc01, hc15, hlam, hphi, ht0b, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3525, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3, h3525, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3621_1]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [h3616, hlam, p3621_0]
                      · have p3621_0 := h3621c.1
                        have p3621_1 := h3621c.2.1
                        have p3621_2 := h3621c.2.2.1
                        have p3621_3 := h3621c.2.2.2
                        linarith only [hlam, p3621_0]
                    · linarith only [h2, h3616, h3617, h3620, h4, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h2, h3616, h3619, h4, hlam]
              · linarith only [h2783, h3524, h3525, h3526, h3616, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3654 | h3654
      · linarith only [h0, h3654, h4, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3656 | h3656
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3657 | h3657
          · linarith only [h1, h2783, h3657, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3659 | h3659
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3660 | h3660
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3661 | h3661
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3662 | h3662
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3663 | h3663
                    · rcases h1bigk with h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c | h3664c
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3656, h3662, hc01, hc45, hlam, hphi, ht0b, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3659, hc01, hc35, hlam, hphi, ht0b, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3657, h3659, hc01, hc35, hlam, hphi, ht0b, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        rcases p3664_3 (m.d 0 1) (by simp) with h3669 | h3669
                        · rcases p3664_3 (m.d 1 2) (by simp) with h3670 | h3670
                          · linarith only [h0, h3670, hlam]
                          · linarith only [h3656, h3670, hlam]
                        · linarith only [h3669, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h0, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3525, hlam, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3654, hlam, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h1, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3657, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h1, h2783, h3656, h3661, h3662, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h2, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h2, h2783, h3525, h3656, h3661, h3662, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h2, h2783, h3656, h3661, h3662, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3664_1]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3656, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3659, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [h3660, hlam, p3664_0]
                      · have p3664_0 := h3664c.1
                        have p3664_1 := h3664c.2.1
                        have p3664_2 := h3664c.2.2.1
                        have p3664_3 := h3664c.2.2.2
                        linarith only [hlam, p3664_0]
                    · linarith only [h2783, h3, h3524, h3656, h3662, h3663, hlam]
                  · linarith only [h1, h2, h2783, h3525, h3656, h3660, h3661, h3662, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3696 | h3696
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3697 | h3697
                    · rcases h1bigk with h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c | h3698c
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3656, h3696, hc01, hc45, hlam, hphi, ht0b, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3525, h3656, h3696, hc01, hc45, hlam, hphi, ht0b, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3654, h3656, h3696, hc01, hc45, hlam, hphi, ht0b, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        rcases p3698_3 (m.d 0 1) (by simp) with h3703 | h3703
                        · rcases p3698_3 (m.d 1 2) (by simp) with h3704 | h3704
                          · linarith only [h0, h3704, hlam]
                          · linarith only [h3656, h3704, hlam]
                        · linarith only [h3703, hlam, p3698_0]
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
                        linarith only [h3525, hlam, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3654, hlam, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h1, hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3657, hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h1, h2783, h3656, h3696, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h2, hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h2, h3656, h3696, hc01, hc45, hlam, hphi, ht0b, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h2, h3656, h3696, hc01, hc45, hlam, hphi, ht0b, ht5b, p3698_1]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3, hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3656, hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3659, hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [h3660, hlam, p3698_0]
                      · have p3698_0 := h3698c.1
                        have p3698_1 := h3698c.2.1
                        have p3698_2 := h3698c.2.2.1
                        have p3698_3 := h3698c.2.2.2
                        linarith only [hlam, p3698_0]
                    · linarith only [h0, h3656, h3661, h3696, h3697, h4, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h3524, h3696, h4, hlam]
              · linarith only [h3525, h3656, h3657, h3660, hlam]
            · linarith only [h3525, h3656, h3659, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h3732 | h3732
          · linarith only [h1, h2783, h3732, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h3734 | h3734
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3735 | h3735
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3736 | h3736
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3737 | h3737
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3738 | h3738
                    · rcases h1bigk with h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c | h3739c
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        rcases p3739_3 (m.d 0 1) (by simp) with h3741 | h3741
                        · rcases p3739_3 (m.d 1 2) (by simp) with h3742 | h3742
                          · linarith only [h3742, hlam, p3739_0]
                          · rcases p3739_3 (m.d 1 3) (by simp) with h3744 | h3744
                            · linarith only [h1, h3744, hlam]
                            · linarith only [h3525, h3744, hlam]
                        · linarith only [h3741, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3734, hc01, hc35, hlam, hphi, ht0b, ht5b, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3732, h3734, h3738, hc01, hc45, hlam, hphi, ht0b, ht5b, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        rcases p3739_3 (m.d 0 1) (by simp) with h3750 | h3750
                        · rcases p3739_3 (m.d 1 2) (by simp) with h3751 | h3751
                          · linarith only [h0, h3751, hlam]
                          · rcases p3739_3 (m.d 1 3) (by simp) with h3753 | h3753
                            · linarith only [h1, h3753, hlam]
                            · linarith only [h3734, h3753, hlam]
                        · linarith only [h3750, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h0, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3525, hlam, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3654, hlam, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3656, hlam, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h1, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3732, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h1, h2783, h3736, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h2, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h2, h2783, h3736, hc12, hc23, hlam, hphi, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h2, h2783, h3736, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h2, h2783, h3656, h3736, hc12, hc23, hlam, hphi, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3739_1]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3734, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [h3735, hlam, p3739_0]
                      · have p3739_0 := h3739c.1
                        have p3739_1 := h3739c.2.1
                        have p3739_2 := h3739c.2.2.1
                        have p3739_3 := h3739c.2.2.2
                        linarith only [hlam, p3739_0]
                    · linarith only [h2783, h3524, h3738, hlam]
                  · linarith only [h1, h2783, h3734, h3735, h3736, h3737, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3779 | h3779
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3780 | h3780
                    · rcases h1bigk with h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c | h3781c
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        rcases p3781_3 (m.d 0 1) (by simp) with h3783 | h3783
                        · rcases p3781_3 (m.d 1 2) (by simp) with h3784 | h3784
                          · linarith only [h3784, hlam, p3781_0]
                          · rcases p3781_3 (m.d 1 3) (by simp) with h3786 | h3786
                            · linarith only [h1, h3786, hlam]
                            · linarith only [h3525, h3786, hlam]
                        · linarith only [h3783, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3734, h3780, hc01, hc45, hlam, hphi, ht0b, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3732, h3734, h3780, hc01, hc45, hlam, hphi, ht0b, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        rcases p3781_3 (m.d 0 1) (by simp) with h3792 | h3792
                        · rcases p3781_3 (m.d 1 2) (by simp) with h3793 | h3793
                          · linarith only [h0, h3793, hlam]
                          · rcases p3781_3 (m.d 1 3) (by simp) with h3795 | h3795
                            · linarith only [h1, h3795, hlam]
                            · linarith only [h3734, h3795, hlam]
                        · linarith only [h3792, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h0, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3525, hlam, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3654, hlam, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3656, hlam, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h1, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3732, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h1, h2783, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h2, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h2, h3656, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3781_1]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3734, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [h3735, hlam, p3781_0]
                      · have p3781_0 := h3781c.1
                        have p3781_1 := h3781c.2.1
                        have p3781_2 := h3781c.2.2.1
                        have p3781_3 := h3781c.2.2.2
                        linarith only [hlam, p3781_0]
                    · linarith only [h3524, h3736, h3780, h4, hlam]
                  · linarith only [h2, h3735, h3779, h4, hlam]
              · linarith only [h3732, h3734, h3735, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h3822 | h3822
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3823 | h3823
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3824 | h3824
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3825 | h3825
                    · rcases h1bigk with h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c | h3826c
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        rcases p3826_3 (m.d 0 1) (by simp) with h3828 | h3828
                        · rcases p3826_3 (m.d 1 2) (by simp) with h3829 | h3829
                          · linarith only [h3829, hlam, p3826_0]
                          · rcases p3826_3 (m.d 1 3) (by simp) with h3831 | h3831
                            · linarith only [h1, h3831, hlam]
                            · linarith only [h3525, h3831, hlam]
                        · linarith only [h3828, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        rcases p3826_3 (m.d 0 1) (by simp) with h3835 | h3835
                        · rcases p3826_3 (m.d 1 2) (by simp) with h3836 | h3836
                          · linarith only [h0, h3836, hlam]
                          · rcases p3826_3 (m.d 1 3) (by simp) with h3838 | h3838
                            · linarith only [h3838, hlam, p3826_0]
                            · rcases p3826_3 (m.d 1 4) (by simp) with h3840 | h3840
                              · linarith only [h2, h3840, hlam]
                              · linarith only [h3732, h3840, hlam]
                        · linarith only [h3835, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3822, hc01, hc45, hlam, hphi, ht0b, ht5b, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        rcases p3826_3 (m.d 0 1) (by simp) with h3845 | h3845
                        · rcases p3826_3 (m.d 1 2) (by simp) with h3846 | h3846
                          · linarith only [h0, h3846, hlam]
                          · rcases p3826_3 (m.d 1 3) (by simp) with h3848 | h3848
                            · linarith only [h1, h3848, hlam]
                            · rcases p3826_3 (m.d 1 4) (by simp) with h3850 | h3850
                              · linarith only [h2, h3850, hlam]
                              · linarith only [h3822, h3850, hlam]
                        · linarith only [h3845, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h0, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3525, hlam, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3654, hlam, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3656, hlam, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h1, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3734, hc12, hc35, hlam, hphi, ht23, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3732, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3734, hlam, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h2, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h2, h2783, h3823, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h2, h2783, h3525, h3734, h3823, hc12, hc23, hlam, hphi, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h2783, h3, h3524, h3525, h3823, hc12, hc23, hlam, hphi, p3826_1]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [h3822, hlam, p3826_0]
                      · have p3826_0 := h3826c.1
                        have p3826_1 := h3826c.2.1
                        have p3826_2 := h3826c.2.2.1
                        have p3826_3 := h3826c.2.2.2
                        linarith only [hlam, p3826_0]
                    · linarith only [h2783, h3524, h3825, hlam]
                  · linarith only [h0, h2, h2783, h3822, h3823, h3824, h4, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3876 | h3876
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3877 | h3877
                    · rcases h1bigk with h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c | h3878c
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        rcases p3878_3 (m.d 0 1) (by simp) with h3880 | h3880
                        · rcases p3878_3 (m.d 1 2) (by simp) with h3881 | h3881
                          · linarith only [h3881, hlam, p3878_0]
                          · rcases p3878_3 (m.d 1 3) (by simp) with h3883 | h3883
                            · linarith only [h1, h3883, hlam]
                            · linarith only [h3525, h3883, hlam]
                        · linarith only [h3880, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        rcases p3878_3 (m.d 0 1) (by simp) with h3887 | h3887
                        · rcases p3878_3 (m.d 1 2) (by simp) with h3888 | h3888
                          · linarith only [h0, h3888, hlam]
                          · rcases p3878_3 (m.d 1 3) (by simp) with h3890 | h3890
                            · linarith only [h3890, hlam, p3878_0]
                            · rcases p3878_3 (m.d 1 4) (by simp) with h3892 | h3892
                              · linarith only [h2, h3892, hlam]
                              · linarith only [h3732, h3892, hlam]
                        · linarith only [h3887, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3822, hc01, hc45, hlam, hphi, ht0b, ht5b, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        rcases p3878_3 (m.d 0 1) (by simp) with h3897 | h3897
                        · rcases p3878_3 (m.d 1 2) (by simp) with h3898 | h3898
                          · linarith only [h0, h3898, hlam]
                          · rcases p3878_3 (m.d 1 3) (by simp) with h3900 | h3900
                            · linarith only [h1, h3900, hlam]
                            · rcases p3878_3 (m.d 1 4) (by simp) with h3902 | h3902
                              · linarith only [h2, h3902, hlam]
                              · linarith only [h3822, h3902, hlam]
                        · linarith only [h3897, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h0, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3525, hlam, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3654, hlam, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3656, hlam, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h1, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3732, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3734, hlam, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h2, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h2, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h2, hc01, hc15, hlam, hphi, ht0b, ht5b, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3, h3524, h3525, h4, hc12, hc24, hlam, hphi, p3878_1]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [h3822, hlam, p3878_0]
                      · have p3878_0 := h3878c.1
                        have p3878_1 := h3878c.2.1
                        have p3878_2 := h3878c.2.2.1
                        have p3878_3 := h3878c.2.2.2
                        linarith only [hlam, p3878_0]
                    · linarith only [h3524, h3823, h3877, h4, hlam]
                  · linarith only [h2, h3822, h3876, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3928 | h3928
                · linarith only [h2783, h3524, h3654, h3822, h3928, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3930 | h3930
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3931 | h3931
                    · rcases h1bigk with h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c | h3932c
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        rcases p3932_3 (m.d 0 1) (by simp) with h3934 | h3934
                        · rcases p3932_3 (m.d 1 2) (by simp) with h3935 | h3935
                          · linarith only [h3935, hlam, p3932_0]
                          · rcases p3932_3 (m.d 1 3) (by simp) with h3937 | h3937
                            · linarith only [h1, h3937, hlam]
                            · linarith only [h3525, h3937, hlam]
                        · linarith only [h3934, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        rcases p3932_3 (m.d 0 1) (by simp) with h3941 | h3941
                        · rcases p3932_3 (m.d 1 2) (by simp) with h3942 | h3942
                          · linarith only [h0, h3942, hlam]
                          · rcases p3932_3 (m.d 1 3) (by simp) with h3944 | h3944
                            · linarith only [h3944, hlam, p3932_0]
                            · rcases p3932_3 (m.d 1 4) (by simp) with h3946 | h3946
                              · linarith only [h2, h3946, hlam]
                              · linarith only [h3732, h3946, hlam]
                        · linarith only [h3941, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        rcases p3932_3 (m.d 0 1) (by simp) with h3950 | h3950
                        · rcases p3932_3 (m.d 1 2) (by simp) with h3951 | h3951
                          · linarith only [h0, h3951, hlam]
                          · rcases p3932_3 (m.d 1 3) (by simp) with h3953 | h3953
                            · linarith only [h1, h3953, hlam]
                            · rcases p3932_3 (m.d 1 4) (by simp) with h3955 | h3955
                              · linarith only [h3955, hlam, p3932_0]
                              · rcases p3932_3 (m.d 1 5) (by simp) with h3957 | h3957
                                · linarith only [h3, h3957, hlam]
                                · linarith only [h3822, h3957, hlam]
                        · linarith only [h3950, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        rcases p3932_3 (m.d 0 1) (by simp) with h3961 | h3961
                        · rcases p3932_3 (m.d 1 2) (by simp) with h3962 | h3962
                          · linarith only [h0, h3962, hlam]
                          · rcases p3932_3 (m.d 1 3) (by simp) with h3964 | h3964
                            · linarith only [h1, h3964, hlam]
                            · rcases p3932_3 (m.d 1 4) (by simp) with h3966 | h3966
                              · linarith only [h2, h3966, hlam]
                              · rcases p3932_3 (m.d 1 5) (by simp) with h3968 | h3968
                                · linarith only [h3968, hlam, p3932_0]
                                · rcases h4bigk with h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c | h3970c
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    rcases p3970_3 (m.d 0 4) (by simp) with h3972 | h3972
                                    · rcases p3970_3 (m.d 1 4) (by simp) with h3973 | h3973
                                      · linarith only [h2, h3973, hlam]
                                      · rcases p3970_3 (m.d 2 4) (by simp) with h3975 | h3975
                                        · rcases p3970_3 (m.d 3 4) (by simp) with h3976 | h3976
                                          · rcases p3970_3 (m.d 4 5) (by simp) with h3977 | h3977
                                            · linarith only [h3524, h3977, hlam]
                                            · linarith only [h3822, h3977, hlam]
                                          · linarith only [h3732, h3976, hlam]
                                        · linarith only [h3654, h3975, hlam]
                                    · linarith only [h2, h3972, hlam]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h4, hlam, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h2783, hlam, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3525, h3732, h3822, h4, hc12, hc24, hlam, hphi, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h2, hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3654, hlam, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3732, hlam, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3822, hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3524, h3525, h3732, h3822, h3928, hc12, hc34, hlam, hphi, ht23, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    rcases p3970_3 (m.d 0 4) (by simp) with h3992 | h3992
                                    · linarith only [h3992, h4, hlam]
                                    · linarith only [h2, h3992, hlam]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3928, hlam, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3525, h3732, h3822, h3928, hc12, hc34, hlam, hphi, ht23, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3524, h3525, h3732, h3822, hc12, hc34, hlam, hphi, ht23, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    rcases p3970_3 (m.d 0 4) (by simp) with h3999 | h3999
                                    · linarith only [h2783, h3999, hlam]
                                    · linarith only [h2, h3999, hlam]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3525, h3732, h3822, hc12, hc34, hlam, hphi, ht23, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3524, hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3524, h3525, h3732, h4, hc12, hc24, hlam, hphi, p3970_1]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3930, hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [h3931, hlam, p3970_0]
                                  · have p3970_0 := h3970c.1
                                    have p3970_1 := h3970c.2.1
                                    have p3970_2 := h3970c.2.2.1
                                    have p3970_3 := h3970c.2.2.2
                                    linarith only [hlam, p3970_0]
                        · linarith only [h3961, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h0, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3525, hlam, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3654, hlam, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3656, hlam, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h1, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3732, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3734, hlam, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h2, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3, h3822, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3822, hlam, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3, hlam, p3932_0]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3, h3525, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3932_1]
                      · have p3932_0 := h3932c.1
                        have p3932_1 := h3932c.2.1
                        have p3932_2 := h3932c.2.2.1
                        have p3932_3 := h3932c.2.2.2
                        linarith only [hlam, p3932_0]
                    · linarith only [h3524, h3928, h3931, h4, hlam]
                  · linarith only [h3524, h3930, h4, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4033 | h4033
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4034 | h4034
      · linarith only [h0, h4, h4034, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4036 | h4036
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4037 | h4037
          · linarith only [h1, h2783, h4037, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4039 | h4039
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4040 | h4040
              · linarith only [h2, h3524, h4040, hlam]
              · linarith only [h4033, h4034, h4039, h4040, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4043 | h4043
              · linarith only [h2, h3524, h4043, hlam]
              · linarith only [h4034, h4036, h4043, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4046 | h4046
          · linarith only [h1, h2783, h4046, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4048 | h4048
            · linarith only [h4033, h4036, h4048, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4050 | h4050
              · linarith only [h0, h2, h3524, h4, h4033, h4050, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4052 | h4052
                · linarith only [h0, h3524, h4, h4033, h4052, hc34, hc45, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4054 | h4054
                  · linarith only [h0, h3524, h4, h4033, h4052, h4054, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h4, h4033, h4054, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4057 | h4057
      · linarith only [h4, h4033, h4057, hc02, hc23, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4059 | h4059
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4060 | h4060
          · linarith only [h1, h2783, h4060, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4062 | h4062
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4063 | h4063
              · linarith only [h1, h2, h2783, h3524, h4033, h4059, h4063, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h4057, h4059, h4063, hlam]
            · linarith only [h4033, h4059, h4062, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4067 | h4067
          · linarith only [h1, h2783, h4067, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4069 | h4069
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4070 | h4070
              · linarith only [h1, h2, h2783, h3524, h4069, h4070, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h4067, h4069, h4070, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4073 | h4073
              · linarith only [h2, h3524, h4073, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4075 | h4075
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4076 | h4076
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4077 | h4077
                    · linarith only [h3524, h4, h4075, h4077, hc02, hc23, hlam, hphi]
                    · linarith only [h1, h2783, h4033, h4076, h4077, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4080 | h4080
                    · linarith only [h4075, h4076, h4080, hlam]
                    · rcases h1bigk with h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        rcases p4082_3 (m.d 0 1) (by simp) with h4084 | h4084
                        · rcases p4082_3 (m.d 1 2) (by simp) with h4085 | h4085
                          · linarith only [h4085, hlam, p4082_0]
                          · rcases p4082_3 (m.d 1 3) (by simp) with h4087 | h4087
                            · linarith only [h1, h4087, hlam]
                            · linarith only [h4033, h4087, hlam]
                        · linarith only [h4084, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        rcases p4082_3 (m.d 0 1) (by simp) with h4091 | h4091
                        · rcases p4082_3 (m.d 1 2) (by simp) with h4092 | h4092
                          · linarith only [h0, h4092, hlam]
                          · rcases p4082_3 (m.d 1 3) (by simp) with h4094 | h4094
                            · linarith only [h4094, hlam, p4082_0]
                            · rcases p4082_3 (m.d 1 4) (by simp) with h4096 | h4096
                              · linarith only [h2, h4096, hlam]
                              · linarith only [h4067, h4096, hlam]
                        · linarith only [h4091, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        rcases p4082_3 (m.d 0 1) (by simp) with h4100 | h4100
                        · rcases p4082_3 (m.d 1 2) (by simp) with h4101 | h4101
                          · linarith only [h0, h4101, hlam]
                          · rcases p4082_3 (m.d 1 3) (by simp) with h4103 | h4103
                            · linarith only [h1, h4103, hlam]
                            · rcases p4082_3 (m.d 1 4) (by simp) with h4105 | h4105
                              · linarith only [h4105, hlam, p4082_0]
                              · rcases p4082_3 (m.d 1 5) (by simp) with h4107 | h4107
                                · linarith only [h3, h4107, hlam]
                                · linarith only [h4073, h4107, hlam]
                        · linarith only [h4100, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        rcases p4082_3 (m.d 0 1) (by simp) with h4111 | h4111
                        · rcases p4082_3 (m.d 1 2) (by simp) with h4112 | h4112
                          · linarith only [h0, h4112, hlam]
                          · rcases p4082_3 (m.d 1 3) (by simp) with h4114 | h4114
                            · linarith only [h1, h4114, hlam]
                            · rcases p4082_3 (m.d 1 4) (by simp) with h4116 | h4116
                              · linarith only [h2, h4116, hlam]
                              · rcases p4082_3 (m.d 1 5) (by simp) with h4118 | h4118
                                · linarith only [h4118, hlam, p4082_0]
                                · rcases h4bigk with h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4, h4033, h4067, h4076, hc12, hc45, hlam, hphi, ht23, ht34, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4, hlam, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h2783, hlam, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h3524, hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h2, hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4057, hlam, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4067, hlam, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4073, hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4076, hc04, hc45, hlam, hphi, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4033, h4067, h4076, hc12, hc45, hlam, hphi, ht23, ht34, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h1, h2783, h4033, h4076, hc12, hc45, hlam, hphi, ht23, ht34, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4076, hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h2, h4033, h4067, h4075, hc12, hc23, hlam, hphi, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4033, h4067, h4075, hc12, hc23, hlam, hphi, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4075, hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h4080, hlam, p4120_0]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    rcases p4120_3 (m.d 0 4) (by simp) with h4141 | h4141
                                    · linarith only [h4141, hlam, p4120_0]
                                    · rcases p4120_3 (m.d 1 4) (by simp) with h4143 | h4143
                                      · linarith only [h4073, h4143, hlam]
                                      · rcases p4120_3 (m.d 2 4) (by simp) with h4145 | h4145
                                        · linarith only [h4076, h4145, hlam]
                                        · linarith only [h4, h4145, hlam]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    rcases p4120_3 (m.d 0 4) (by simp) with h4148 | h4148
                                    · linarith only [h3524, h4148, hlam]
                                    · linarith only [h2, h4148, hlam]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h0, h4, hc12, hc45, hlam, hphi, ht23, ht34, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [h1, h2783, h4033, hc12, hc45, hlam, hphi, ht23, ht34, p4120_1]
                                  · have p4120_0 := h4120c.1
                                    have p4120_1 := h4120c.2.1
                                    have p4120_2 := h4120c.2.2.1
                                    have p4120_3 := h4120c.2.2.2
                                    linarith only [hlam, p4120_0]
                        · linarith only [h4111, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h0, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h4033, hlam, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h4057, hlam, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h4059, hlam, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h1, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h1, h2783, h4075, hc12, hc24, hlam, hphi, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h4067, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h4069, hlam, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h2, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h2, h3524, hc12, hc45, hlam, hphi, ht23, ht34, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h2, h3524, hc13, hc45, hlam, hphi, ht34, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h4073, hlam, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h3, hlam, p4082_0]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h3, h4033, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4082_1]
                      · have p4082_0 := h4082c.1
                        have p4082_1 := h4082c.2.1
                        have p4082_2 := h4082c.2.2.1
                        have p4082_3 := h4082c.2.2.2
                        linarith only [hlam, p4082_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4175 | h4175
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4176 | h4176
                    · rcases h1bigk with h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c | h4177c
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        rcases p4177_3 (m.d 0 1) (by simp) with h4179 | h4179
                        · rcases p4177_3 (m.d 1 2) (by simp) with h4180 | h4180
                          · linarith only [h4180, hlam, p4177_0]
                          · rcases p4177_3 (m.d 1 3) (by simp) with h4182 | h4182
                            · linarith only [h1, h4182, hlam]
                            · linarith only [h4033, h4182, hlam]
                        · linarith only [h4179, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        rcases p4177_3 (m.d 0 1) (by simp) with h4186 | h4186
                        · rcases p4177_3 (m.d 1 2) (by simp) with h4187 | h4187
                          · linarith only [h0, h4187, hlam]
                          · rcases p4177_3 (m.d 1 3) (by simp) with h4189 | h4189
                            · linarith only [h4189, hlam, p4177_0]
                            · rcases p4177_3 (m.d 1 4) (by simp) with h4191 | h4191
                              · linarith only [h2, h4191, hlam]
                              · linarith only [h4067, h4191, hlam]
                        · linarith only [h4186, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        rcases p4177_3 (m.d 0 1) (by simp) with h4195 | h4195
                        · rcases p4177_3 (m.d 1 2) (by simp) with h4196 | h4196
                          · linarith only [h0, h4196, hlam]
                          · rcases p4177_3 (m.d 1 3) (by simp) with h4198 | h4198
                            · linarith only [h1, h4198, hlam]
                            · rcases p4177_3 (m.d 1 4) (by simp) with h4200 | h4200
                              · linarith only [h4200, hlam, p4177_0]
                              · rcases p4177_3 (m.d 1 5) (by simp) with h4202 | h4202
                                · linarith only [h3, h4202, hlam]
                                · linarith only [h4073, h4202, hlam]
                        · linarith only [h4195, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        rcases p4177_3 (m.d 0 1) (by simp) with h4206 | h4206
                        · rcases p4177_3 (m.d 1 2) (by simp) with h4207 | h4207
                          · linarith only [h0, h4207, hlam]
                          · rcases p4177_3 (m.d 1 3) (by simp) with h4209 | h4209
                            · linarith only [h1, h4209, hlam]
                            · rcases p4177_3 (m.d 1 4) (by simp) with h4211 | h4211
                              · linarith only [h2, h4211, hlam]
                              · rcases p4177_3 (m.d 1 5) (by simp) with h4213 | h4213
                                · linarith only [h4213, hlam, p4177_0]
                                · rcases h4bigk with h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c | h4215c
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h3524, h4033, h4067, h4075, h4175, hc12, hc34, hlam, hphi, ht23, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4, hlam, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h2783, hlam, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h3524, hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h2, hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4057, hlam, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4067, hlam, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4073, hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    rcases p4215_3 (m.d 0 4) (by simp) with h4226 | h4226
                                    · linarith only [h4, h4226, hlam]
                                    · rcases p4215_3 (m.d 1 4) (by simp) with h4228 | h4228
                                      · linarith only [h4057, h4228, hlam]
                                      · rcases p4215_3 (m.d 2 4) (by simp) with h4230 | h4230
                                        · rcases p4215_3 (m.d 3 4) (by simp) with h4231 | h4231
                                          · rcases p4215_3 (m.d 4 5) (by simp) with h4232 | h4232
                                            · linarith only [h4175, h4232, hlam]
                                            · linarith only [h3524, h4232, hlam]
                                          · linarith only [h2783, h4231, hlam]
                                        · linarith only [h4, h4230, hlam]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    rcases p4215_3 (m.d 0 4) (by simp) with h4237 | h4237
                                    · linarith only [h4, h4237, hlam]
                                    · linarith only [h2, h4237, hlam]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4075, hlam, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h2783, h3524, h4075, hc03, hc34, hlam, hphi, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    rcases p4215_3 (m.d 0 4) (by simp) with h4243 | h4243
                                    · linarith only [h2783, h4243, hlam]
                                    · rcases p4215_3 (m.d 1 4) (by simp) with h4245 | h4245
                                      · linarith only [h4067, h4245, hlam]
                                      · rcases p4215_3 (m.d 2 4) (by simp) with h4247 | h4247
                                        · linarith only [h4075, h4247, hlam]
                                        · linarith only [h4, h4247, hlam]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    rcases p4215_3 (m.d 0 4) (by simp) with h4250 | h4250
                                    · linarith only [h2783, h4250, hlam]
                                    · linarith only [h2, h4250, hlam]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h1, h2783, h3524, h4033, hc12, hc34, hlam, hphi, ht23, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h1, h2783, h4033, h4175, hc12, hc24, hlam, hphi, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4033, h4067, h4175, hc12, hc24, hlam, hphi, p4215_1]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4175, hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [h4176, hlam, p4215_0]
                                  · have p4215_0 := h4215c.1
                                    have p4215_1 := h4215c.2.1
                                    have p4215_2 := h4215c.2.2.1
                                    have p4215_3 := h4215c.2.2.2
                                    linarith only [hlam, p4215_0]
                        · linarith only [h4206, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h0, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h4033, hlam, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h4057, hlam, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h4059, hlam, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h1, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h4067, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h4069, hlam, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h2, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h2, h3524, h4175, hc12, hc24, hlam, hphi, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h2, h3524, h4175, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h4073, hlam, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h3, hlam, p4177_0]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h3, h3524, h4033, h4175, hc12, hc24, hlam, hphi, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [h3, h3524, h4175, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4177_1]
                      · have p4177_0 := h4177c.1
                        have p4177_1 := h4177c.2.1
                        have p4177_2 := h4177c.2.2.1
                        have p4177_3 := h4177c.2.2.2
                        linarith only [hlam, p4177_0]
                    · linarith only [h4075, h4175, h4176, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4283 | h4283
                    · linarith only [h0, h4, h4175, h4283, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4033, h4075, h4283, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8564000 in
set_option maxHeartbeats 8564000 in
theorem r1l7_21_14_H_I_L_I_s3_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h2783 | h2783
  · exact r1l7_21_14_H_I_L_I_s3_x1_x0 m hb1 hb4 hg0 hg1 hg2 hg3 h4 h2783
  · exact r1l7_21_14_H_I_L_I_s3_x1_x1 m hb1 hb4 hg0 hg1 hg2 hg3 h4 h2783

set_option maxHeartbeats 8564000 in
set_option maxHeartbeats 8564000 in
theorem r1l7_21_14_H_I_L_I_s3 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_21_14_H_I_L_I_s3_x0 m hb1 hb4 hg0 hg1 hg2 hg3 h4
  · exact r1l7_21_14_H_I_L_I_s3_x1 m hb1 hb4 hg0 hg1 hg2 hg3 h4

end R2N4
