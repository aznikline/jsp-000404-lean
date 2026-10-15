import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_42S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h525 | h525
  · rcases m.htr 1 2 3 (by decide) (by decide) with h526 | h526
    · rcases m.htr 1 2 4 (by decide) (by decide) with h527 | h527
      · rcases m.htr 1 2 5 (by decide) (by decide) with h528 | h528
        · rcases m.htr 1 3 4 (by decide) (by decide) with h529 | h529
          · linarith only [h1, h5, h529, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h531 | h531
            · rcases m.htr 2 3 4 (by decide) (by decide) with h532 | h532
              · linarith only [h0, h1, h5, h526, h531, h532, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h534 | h534
                · rcases m.htr 2 4 5 (by decide) (by decide) with h535 | h535
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h536 | h536
                    · rcases h2bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h527, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h0, h534, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h0, h532, h534, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        rcases p537_3 (m.d 0 2) (by simp) with h542 | h542
                        · rcases p537_3 (m.d 1 2) (by simp) with h543 | h543
                          · linarith only [h0, h543, hlam]
                          · linarith only [h528, h543, hlam]
                        · linarith only [h542, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h0, hlam, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h534, h536, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h0, h532, h534, h536, hc01, hc45, hlam, hphi, ht0b, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h2, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h526, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h532, hlam, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h1, h5, h526, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h3, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h527, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h534, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h0, h527, h534, hc01, hc35, hlam, hphi, ht0b, ht5b, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h4, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h528, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h534, hlam, p537_0]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [h535, hlam, p537_1]
                      · have p537_0 := h537c.1
                        have p537_1 := h537c.2.1
                        have p537_2 := h537c.2.2.1
                        have p537_3 := h537c.2.2.2
                        linarith only [hlam, p537_0]
                    · linarith only [h1, h5, h526, h534, h536, hc35, hlam, hphi, u5elo4]
                  · linarith only [h532, h534, h535, hc35, hlam, hphi, u5elo4]
                · linarith only [h5, h525, h534, hc23, hc34, hlam, hphi]
            · linarith only [h5, h525, h531, hc13, hc34, hlam, hphi]
        · linarith only [h4, h526, h528, hc23, hlam, hphi, ht34, ht45, u5elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h572 | h572
        · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
          · linarith only [h1, h5, h525, h573, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h575 | h575
            · rcases m.htr 2 3 4 (by decide) (by decide) with h576 | h576
              · linarith only [h3, h5, h526, h527, h576, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h578 | h578
                · linarith only [h0, h3, h526, h527, h578, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h1, h5, h575, h578, hc23, hc34, hlam, hphi]
            · linarith only [h5, h525, h575, hc13, hc34, hlam, hphi]
        · linarith only [h4, h526, h572, hc23, hlam, hphi, ht34, ht45, u5elo0]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h583 | h583
      · rcases m.htr 1 2 5 (by decide) (by decide) with h584 | h584
        · rcases m.htr 1 3 4 (by decide) (by decide) with h585 | h585
          · linarith only [h2, h5, h526, h583, h585, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h526, h583, h585, hlam]
        · linarith only [h583, h584, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h589 | h589
        · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
          · linarith only [h1, h5, h525, h590, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h592 | h592
            · rcases m.htr 2 3 4 (by decide) (by decide) with h593 | h593
              · linarith only [h2, h5, h593, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h595 | h595
                · rcases m.htr 2 4 5 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h597 | h597
                    · rcases h2bigk with h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c | h598c
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, h589, h595, h597, hc01, hc45, hlam, hphi, ht0b, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, h526, h589, h595, h597, hc01, hc45, hlam, hphi, ht0b, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, h526, h583, h589, h590, h595, h597, hc01, hc45, hlam, hphi, ht0b, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        rcases p598_3 (m.d 0 2) (by simp) with h603 | h603
                        · rcases p598_3 (m.d 1 2) (by simp) with h604 | h604
                          · linarith only [h0, h604, hlam]
                          · linarith only [h589, h604, hlam]
                        · linarith only [h603, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, hlam, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h526, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h583, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h2, h5, h526, h595, h597, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h2, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h593, hlam, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h2, h5, h595, h597, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h3, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h589, h595, h597, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h0, h3, h595, h597, hc01, hc45, hlam, hphi, ht0b, ht5b, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h4, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h589, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h595, hlam, p598_0]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [h596, hlam, p598_1]
                      · have p598_0 := h598c.1
                        have p598_1 := h598c.2.1
                        have p598_2 := h598c.2.2.1
                        have p598_3 := h598c.2.2.2
                        linarith only [hlam, p598_0]
                    · linarith only [h2, h5, h526, h589, h595, h597, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                  · linarith only [h583, h589, h595, h596, hc35, hlam, hphi, u5elo4]
                · linarith only [h526, h589, h595, hc25, hlam, hphi, u5elo3]
            · linarith only [h5, h525, h526, h589, h592, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h632 | h632
          · linarith only [h1, h5, h525, h632, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h634 | h634
            · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
              · linarith only [h2, h5, h635, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h637 | h637
                · rcases m.htr 2 4 5 (by decide) (by decide) with h638 | h638
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h639 | h639
                    · rcases h2bigk with h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c | h640c
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        rcases p640_3 (m.d 0 2) (by simp) with h642 | h642
                        · rcases p640_3 (m.d 1 2) (by simp) with h643 | h643
                          · linarith only [h0, h643, hlam]
                          · rcases p640_3 (m.d 2 3) (by simp) with h645 | h645
                            · linarith only [h2, h645, hlam]
                            · linarith only [h526, h645, hlam]
                        · linarith only [h0, h642, hlam]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h526, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h583, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h589, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, hlam, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h526, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h583, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h589, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h2, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hc12, hc23, hlam, hphi, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h635, hlam, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h589, hc12, hc23, hlam, hphi, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h3, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h526, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h0, h3, h589, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h4, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h637, hc12, hc23, hlam, hphi, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h637, hlam, p640_0]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [h638, hlam, p640_1]
                      · have p640_0 := h640c.1
                        have p640_1 := h640c.2.1
                        have p640_2 := h640c.2.2.1
                        have p640_3 := h640c.2.2.2
                        linarith only [hlam, p640_0]
                    · linarith only [h5, h639, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h583, h638, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                · linarith only [h526, h637, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · linarith only [h5, h525, h634, hc13, hc34, hlam, hphi]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
    · rcases m.htr 1 2 4 (by decide) (by decide) with h677 | h677
      · rcases m.htr 1 2 5 (by decide) (by decide) with h678 | h678
        · rcases m.htr 1 3 4 (by decide) (by decide) with h679 | h679
          · linarith only [h1, h525, h679, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h681 | h681
            · linarith only [h1, h525, h681, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h683 | h683
              · linarith only [h0, h1, h5, h676, h683, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h685 | h685
                · linarith only [h1, h525, h676, h685, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h687 | h687
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h688 | h688
                    · rcases h2bigk with h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c | h689c
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, h677, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        rcases p689_3 (m.d 0 2) (by simp) with h692 | h692
                        · rcases p689_3 (m.d 1 2) (by simp) with h693 | h693
                          · linarith only [h0, h693, hlam]
                          · linarith only [h676, h693, hlam]
                        · linarith only [h692, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, h687, hc01, hc45, hlam, hphi, ht0b, ht5b, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        rcases p689_3 (m.d 0 2) (by simp) with h698 | h698
                        · rcases p689_3 (m.d 1 2) (by simp) with h699 | h699
                          · linarith only [h0, h699, hlam]
                          · linarith only [h678, h699, hlam]
                        · linarith only [h698, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, h687, hc01, hc45, hlam, hphi, ht0b, ht5b, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h2, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h676, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h683, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h685, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h3, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h677, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h0, h677, h685, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h4, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h678, hlam, p689_0]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hc23, hlam, hphi, ht34, ht45, p689_1, u5elo2]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [h687, hlam, p689_1]
                      · have p689_0 := h689c.1
                        have p689_1 := h689c.2.1
                        have p689_2 := h689c.2.2.1
                        have p689_3 := h689c.2.2.2
                        linarith only [hlam, p689_0]
                    · linarith only [h5, h688, hc03, hlam, hphi, ht34, ht45, u5elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h724 | h724
                    · rcases h2bigk with h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c | h725c
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h0, h676, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        rcases p725_3 (m.d 0 2) (by simp) with h728 | h728
                        · rcases p725_3 (m.d 1 2) (by simp) with h729 | h729
                          · linarith only [h0, h729, hlam]
                          · linarith only [h676, h729, hlam]
                        · linarith only [h728, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        rcases p725_3 (m.d 0 2) (by simp) with h733 | h733
                        · rcases p725_3 (m.d 1 2) (by simp) with h734 | h734
                          · linarith only [h0, h734, hlam]
                          · linarith only [h677, h734, hlam]
                        · linarith only [h733, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        rcases p725_3 (m.d 0 2) (by simp) with h738 | h738
                        · rcases p725_3 (m.d 1 2) (by simp) with h739 | h739
                          · linarith only [h0, h739, hlam]
                          · linarith only [h678, h739, hlam]
                        · linarith only [h738, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h0, hlam, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h0, h683, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h2, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h676, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h683, hlam, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h685, hlam, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h3, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h677, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h687, h724, hc23, hc34, hlam, hphi, p725_1]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h687, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h4, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h678, hlam, p725_0]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [hc23, hlam, hphi, ht34, ht45, p725_1, u5elo2]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [h4, h525, hc24, hlam, hphi, ht45, p725_1, u5elo3]
                      · have p725_0 := h725c.1
                        have p725_1 := h725c.2.1
                        have p725_2 := h725c.2.2.1
                        have p725_3 := h725c.2.2.2
                        linarith only [hlam, p725_0]
                    · linarith only [h1, h5, h676, h724, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h4, h525, h676, h678, hc23, hlam, hphi, ht34, ht45, u5elo3]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h765 | h765
        · rcases m.htr 1 3 4 (by decide) (by decide) with h766 | h766
          · linarith only [h1, h3, h5, h676, h677, h766, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h768 | h768
            · linarith only [h1, h525, h768, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h770 | h770
              · linarith only [h2, h525, h770, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h772 | h772
                · linarith only [h0, h3, h525, h676, h677, h772, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h775 | h775
                    · rcases h2bigk with h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c | h776c
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h0, h765, hc01, hc25, hlam, hphi, ht0b, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        rcases p776_3 (m.d 0 2) (by simp) with h779 | h779
                        · rcases p776_3 (m.d 1 2) (by simp) with h780 | h780
                          · linarith only [h0, h780, hlam]
                          · linarith only [h676, h780, hlam]
                        · linarith only [h779, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h0, h677, h765, h772, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        rcases p776_3 (m.d 0 2) (by simp) with h785 | h785
                        · rcases p776_3 (m.d 1 2) (by simp) with h786 | h786
                          · linarith only [h0, h786, hlam]
                          · linarith only [h765, h786, hlam]
                        · linarith only [h785, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h0, hlam, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h3, h677, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h677, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h0, h3, h677, h772, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h2, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h676, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h770, hlam, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h772, hlam, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h3, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h0, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h0, h3, h772, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h4, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h765, hlam, p776_0]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h765, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [h774, hlam, p776_1]
                      · have p776_0 := h776c.1
                        have p776_1 := h776c.2.1
                        have p776_2 := h776c.2.2.1
                        have p776_3 := h776c.2.2.2
                        linarith only [hlam, p776_0]
                    · linarith only [h3, h5, h677, h775, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h677, h765, h772, h774, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h4, h525, h676, h765, hc23, hlam, hphi, ht34, ht45, u5elo3]
    · linarith only [h2, h525, h676, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h4 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h2, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h815 | h815
  · rcases m.htr 0 3 4 (by decide) (by decide) with h816 | h816
    · linarith only [h2, h3, h816, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h818 | h818
      · rcases m.htr 1 2 3 (by decide) (by decide) with h819 | h819
        · rcases m.htr 1 2 4 (by decide) (by decide) with h820 | h820
          · linarith only [h0, h3, h820, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h822 | h822
            · rcases m.htr 1 3 4 (by decide) (by decide) with h823 | h823
              · linarith only [h1, h816, h818, h823, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h825 | h825
                · rcases m.htr 2 3 4 (by decide) (by decide) with h826 | h826
                  · linarith only [h0, h1, h816, h819, h825, h826, hc02, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h828 | h828
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h829 | h829
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h830 | h830
                        · rcases h2bigk with h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c | h831c
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h3, h826, hc12, hc34, hlam, hphi, ht23, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h3, h826, h828, h830, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h3, hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h3, h826, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h0, hlam, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h828, h830, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h820, hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h0, h3, h826, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h2, hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h819, hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h826, hlam, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h1, h819, hc01, hc25, hlam, hphi, ht0b, ht5b, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h826, hc02, hc34, hlam, hphi, ht23, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h819, h826, hc23, hc34, hlam, hphi, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h826, hc23, hc34, hlam, hphi, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            rcases p831_3 (m.d 0 2) (by simp) with h851 | h851
                            · linarith only [h3, h851, hlam]
                            · linarith only [h815, h851, hlam]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h815, hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h822, hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h828, hlam, p831_0]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [h829, hlam, p831_1]
                          · have p831_0 := h831c.1
                            have p831_1 := h831c.2.1
                            have p831_2 := h831c.2.2.1
                            have p831_3 := h831c.2.2.2
                            linarith only [hlam, p831_0]
                        · linarith only [h3, h826, h830, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h3, h819, h828, h829, hc35, hlam, hphi, u5elo4]
                    · linarith only [h2, h3, h818, h826, h828, hc23, hc34, hlam, hphi]
                · linarith only [h816, h818, h825, hc13, hc34, hlam, hphi]
            · linarith only [h3, h815, h822, hc12, hc24, hlam, hphi]
        · linarith only [h2, h3, h819, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h865 | h865
        · rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
          · linarith only [h0, h3, h815, h866, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
            · rcases m.htr 1 3 4 (by decide) (by decide) with h869 | h869
              · linarith only [h1, h818, h869, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h871 | h871
                · linarith only [h1, h818, h871, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h873 | h873
                  · linarith only [h2, h818, h869, h873, hc14, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h875 | h875
                    · linarith only [h0, h1, h818, h865, h875, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h877 | h877
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h878 | h878
                        · rcases h2bigk with h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c | h879c
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h3, h873, hc12, hc34, hlam, hphi, ht23, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h3, h873, hc23, hc34, hlam, hphi, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h3, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h3, h873, h875, hc23, hc34, hlam, hphi, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h0, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h866, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h0, h3, h873, h875, hc23, hc34, hlam, hphi, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h2, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h865, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h873, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h875, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h873, hc02, hc34, hlam, hphi, ht23, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h865, h873, hc23, hc34, hlam, hphi, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h873, hc23, hc34, hlam, hphi, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h873, h875, hc23, hc34, hlam, hphi, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h815, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h868, hlam, p879_0]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h0, h868, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [h877, hlam, p879_1]
                          · have p879_0 := h879c.1
                            have p879_1 := h879c.2.1
                            have p879_2 := h879c.2.2.1
                            have p879_3 := h879c.2.2.2
                            linarith only [hlam, p879_0]
                        · linarith only [h0, h3, h868, h873, h877, h878, hlam]
                      · linarith only [h0, h3, h868, h877, hc25, hlam, hphi, u5elo4]
            · linarith only [h865, h868, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · linarith only [h2, h3, h865, hc12, hc24, hlam, hphi]
  · linarith only [h2, h815, hc23, hlam, hphi, ht34, ht45, u5elo2]

set_option maxHeartbeats 6562000 in
set_option maxHeartbeats 6562000 in
theorem r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x0 m hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_22_13_15_H_I_L_I_L_0_x0_x0_x0_x1 m hb2 hb3 hb5 h0 h1 h2 h3

end R2N4
