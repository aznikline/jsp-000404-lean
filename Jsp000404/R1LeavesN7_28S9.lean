import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
  · linarith only [h6, h620, h7, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
    · rcases m.htr 1 2 4 (by decide) (by decide) with h623 | h623
      · rcases m.htr 1 2 5 (by decide) (by decide) with h624 | h624
        · rcases m.htr 1 3 4 (by decide) (by decide) with h625 | h625
          · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
            · linarith only [h1, h626, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h628 | h628
              · linarith only [h1, h4, h620, h625, h628, h7, hc35, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h630 | h630
                · rcases m.htr 2 3 5 (by decide) (by decide) with h631 | h631
                  · linarith only [h3, h631, h7, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h633 | h633
                    · linarith only [h4, h620, h633, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h635 | h635
                      · linarith only [h4, h620, h635, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h0bigk with h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c | h637c
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h3, h630, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, u2ehi3]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          rcases p637_3 (m.d 0 1) (by simp) with h640 | h640
                          · rcases p637_3 (m.d 0 2) (by simp) with h641 | h641
                            · linarith only [h0, h641, hlam]
                            · linarith only [h3, h641, hlam]
                          · linarith only [h1, h640, hlam]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          rcases p637_3 (m.d 0 1) (by simp) with h645 | h645
                          · rcases p637_3 (m.d 0 2) (by simp) with h646 | h646
                            · linarith only [h0, h646, hlam]
                            · linarith only [h4, h646, hlam]
                          · linarith only [h645, hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          rcases p637_3 (m.d 0 1) (by simp) with h650 | h650
                          · rcases p637_3 (m.d 0 2) (by simp) with h651 | h651
                            · linarith only [h0, h651, hlam]
                            · linarith only [h5, h651, hlam]
                          · linarith only [h2, h650, hlam]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h0, hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          rcases p637_3 (m.d 0 1) (by simp) with h657 | h657
                          · rcases p637_3 (m.d 0 2) (by simp) with h658 | h658
                            · rcases p637_3 (m.d 0 3) (by simp) with h659 | h659
                              · linarith only [h3, h659, hlam]
                              · rcases p637_3 (m.d 0 4) (by simp) with h661 | h661
                                · linarith only [h4, h661, hlam]
                                · rcases p637_3 (m.d 0 5) (by simp) with h663 | h663
                                  · linarith only [h5, h663, hlam]
                                  · linarith only [h663, h7, hlam]
                            · linarith only [h3, h658, hlam]
                          · linarith only [h1, h657, hlam]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          rcases p637_3 (m.d 0 1) (by simp) with h668 | h668
                          · rcases p637_3 (m.d 0 2) (by simp) with h669 | h669
                            · rcases p637_3 (m.d 0 3) (by simp) with h670 | h670
                              · linarith only [h3, h670, hlam]
                              · linarith only [h6, h670, hlam]
                            · linarith only [h4, h669, hlam]
                          · linarith only [h0, h668, hlam, p637_1]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          rcases p637_3 (m.d 0 1) (by simp) with h675 | h675
                          · rcases p637_3 (m.d 0 2) (by simp) with h676 | h676
                            · rcases p637_3 (m.d 0 3) (by simp) with h677 | h677
                              · linarith only [h3, h677, hlam]
                              · rcases p637_3 (m.d 0 4) (by simp) with h679 | h679
                                · linarith only [h4, h679, hlam]
                                · rcases p637_3 (m.d 0 5) (by simp) with h681 | h681
                                  · linarith only [h5, h681, hlam]
                                  · rcases h0emax with h683 | h683 | h683 | h683 | h683
                                    · linarith only [h0, h1, h623, h625, h683, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, u2ehi3]
                                    · linarith only [h1, h623, h625, h683, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, u2ehi3]
                                    · rcases h5bigk with h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c | h686c
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [hlam, p686_0]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h0, h623, h625, h626, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h0, h630, h631, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h7, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h620, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h2, hlam, p686_0]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [hlam, p686_0]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h630, h631, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h626, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h628, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h5, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h624, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [hlam, p686_0]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h631, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h633, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h5, h630, h631, h635, hc45, hlam, hphi, ht23, ht34, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h624, h630, h631, h635, hc45, hlam, hphi, ht23, ht34, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h630, h631, h635, hc45, hlam, hphi, ht23, ht34, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [hlam, p686_0]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h635, hlam, p686_1]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h1, h623, h625, h7, hc45, hlam, hphi, ht23, ht34, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h624, h630, h631, hc45, hlam, hphi, ht23, ht34, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h630, h631, hc45, hlam, hphi, ht23, ht34, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [h1, h623, h625, h7, hc45, hlam, hphi, ht23, ht34, p686_1, u2ehi3]
                                      · have p686_0 := h686c.1
                                        have p686_1 := h686c.2.1
                                        have p686_2 := h686c.2.2.1
                                        have p686_3 := h686c.2.2.2
                                        linarith only [hlam, p686_0]
                                    · rcases h5bigk with h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c | h712c
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [hlam, p712_0]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h624, h630, h631, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h0, h630, h631, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h7, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h620, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h2, hlam, p712_0]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [hlam, p712_0]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h630, h631, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h626, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h628, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h5, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h624, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [hlam, p712_0]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h631, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h633, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h5, h630, h631, hc35, hlam, hphi, ht23, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h624, h630, h631, hc35, hlam, hphi, ht23, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h630, h631, hc35, hlam, hphi, ht23, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [hlam, p712_0]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h635, hlam, p712_1]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h1, h623, h625, h7, hc45, hlam, hphi, ht23, ht34, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h624, h630, h631, hc45, hlam, hphi, ht23, ht34, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h630, h631, hc45, hlam, hphi, ht23, ht34, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [h1, h623, h625, h7, hc45, hlam, hphi, ht23, ht34, p712_1, u2ehi3]
                                      · have p712_0 := h712c.1
                                        have p712_1 := h712c.2.1
                                        have p712_2 := h712c.2.2.1
                                        have p712_3 := h712c.2.2.2
                                        linarith only [hlam, p712_0]
                                    · rcases h5bigk with h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c | h738c
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h624, h630, h631, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h0, h630, h631, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h7, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h620, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h2, hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h630, h631, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h626, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h628, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h5, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h624, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h631, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h633, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h5, h630, h631, hc35, hlam, hphi, ht23, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h624, h630, h631, hc35, hlam, hphi, ht23, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h630, h631, hc35, hlam, hphi, ht23, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h635, hlam, p738_1]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h1, h623, h625, h7, hc45, hlam, hphi, ht23, ht34, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h624, h630, h631, hc45, hlam, hphi, ht23, ht34, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h630, h631, hc45, hlam, hphi, ht23, ht34, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [h1, h623, h625, h7, hc45, hlam, hphi, ht23, ht34, p738_1, u2ehi3]
                                      · have p738_0 := h738c.1
                                        have p738_1 := h738c.2.1
                                        have p738_2 := h738c.2.2.1
                                        have p738_3 := h738c.2.2.2
                                        linarith only [hlam, p738_0]
                            · linarith only [h5, h676, hlam]
                          · linarith only [h2, h675, hlam]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h1, hlam, p637_1]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h3, hlam, p637_1]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h4, h7, hc35, hlam, hphi, ht23, p637_1, u2ehi3]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h7, hlam, p637_1]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h0, h624, h630, h631, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p637_1, u2ehi3]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h4, hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h6, hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h620, hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h2, hlam, p637_0]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h5, hlam, p637_1]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h1, h623, h625, h635, h7, hc45, hlam, hphi, ht23, ht34, p637_1, u2ehi3]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [h4, h635, h7, hc45, hlam, hphi, ht23, ht34, p637_1, u2ehi3]
                        · have p637_0 := h637c.1
                          have p637_1 := h637c.2.1
                          have p637_2 := h637c.2.2.1
                          have p637_3 := h637c.2.2.2
                          linarith only [hlam, p637_0]
                · linarith only [h6, h630, h7, hc23, hc35, hlam, hphi]
          · linarith only [h6, h625, h7, hc13, hc35, hlam, hphi]
        · linarith only [h622, h624, hc25, hlam, hphi, u2ehi2]
      · linarith only [h622, h623, hc24, hlam, hphi, u2ehi2]
    · linarith only [h3, h622, h7, hc35, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5 h6 h7
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
  · rcases m.htr 0 4 5 (by decide) (by decide) with h787 | h787
    · rcases m.htr 1 2 3 (by decide) (by decide) with h788 | h788
      · rcases m.htr 1 2 4 (by decide) (by decide) with h789 | h789
        · rcases m.htr 1 2 5 (by decide) (by decide) with h790 | h790
          · rcases m.htr 1 3 4 (by decide) (by decide) with h791 | h791
            · linarith only [h1, h6, h786, h791, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h793 | h793
              · rcases m.htr 1 4 5 (by decide) (by decide) with h794 | h794
                · rcases m.htr 2 3 4 (by decide) (by decide) with h795 | h795
                  · linarith only [h2, h6, h786, h790, h795, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h797 | h797
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h798 | h798
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h799 | h799
                        · rcases h0bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h0, h789, h795, h797, hc01, hc35, hlam, hphi, ht0b, ht5b, p800_1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            rcases p800_3 (m.d 0 1) (by simp) with h803 | h803
                            · rcases p800_3 (m.d 0 2) (by simp) with h804 | h804
                              · linarith only [h0, h804, hlam]
                              · linarith only [h3, h804, hlam]
                            · linarith only [h1, h803, hlam]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            rcases p800_3 (m.d 0 1) (by simp) with h808 | h808
                            · rcases p800_3 (m.d 0 2) (by simp) with h809 | h809
                              · linarith only [h0, h809, hlam]
                              · linarith only [h4, h809, hlam]
                            · linarith only [h808, hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            rcases p800_3 (m.d 0 1) (by simp) with h813 | h813
                            · rcases p800_3 (m.d 0 2) (by simp) with h814 | h814
                              · linarith only [h0, h814, hlam]
                              · linarith only [h5, h814, hlam]
                            · linarith only [h2, h813, hlam]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h0, hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            rcases p800_3 (m.d 0 1) (by simp) with h820 | h820
                            · rcases p800_3 (m.d 0 2) (by simp) with h821 | h821
                              · rcases p800_3 (m.d 0 3) (by simp) with h822 | h822
                                · linarith only [h3, h822, hlam]
                                · rcases p800_3 (m.d 0 4) (by simp) with h824 | h824
                                  · linarith only [h4, h824, hlam]
                                  · linarith only [h6, h824, hlam]
                              · linarith only [h3, h821, hlam]
                            · linarith only [h1, h820, hlam]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            rcases p800_3 (m.d 0 1) (by simp) with h829 | h829
                            · rcases p800_3 (m.d 0 2) (by simp) with h830 | h830
                              · rcases p800_3 (m.d 0 3) (by simp) with h831 | h831
                                · linarith only [h3, h831, hlam]
                                · rcases p800_3 (m.d 0 4) (by simp) with h833 | h833
                                  · linarith only [h4, h833, hlam]
                                  · rcases p800_3 (m.d 0 5) (by simp) with h835 | h835
                                    · linarith only [h5, h835, hlam]
                                    · rcases h0emax with h837 | h837 | h837 | h837 | h837
                                      · linarith only [h0, h789, h795, h797, h837, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                      · linarith only [h2, h6, h786, h790, h837, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi4]
                                      · rcases h5bigk with h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c | h840c
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h6, h786, h790, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, p840_1, u2ehi4]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, p840_1, u2ehi4]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h6, h786, h799, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h2, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h793, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p840_1, u2ehi4]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h1, h6, h793, h799, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h1, h6, h793, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h5, hlam, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h790, hlam, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h789, h795, h797, h799, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h1, h6, h788, h797, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h786, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h793, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h797, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p840_1]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h787, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h794, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h798, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [h799, hlam, p840_0]
                                        · have p840_0 := h840c.1
                                          have p840_1 := h840c.2.1
                                          have p840_2 := h840c.2.2.1
                                          have p840_3 := h840c.2.2.2
                                          linarith only [hlam, p840_0]
                                      · rcases h5bigk with h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc15, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc25, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc35, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h2, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p866_1, u2ehi4]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h2, h6, h786, hc01, hc35, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h2, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h5, hlam, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h790, hlam, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h2, h6, h786, h790, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h786, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h793, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h797, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p866_1]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h787, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h794, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h798, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [h799, hlam, p866_0]
                                        · have p866_0 := h866c.1
                                          have p866_1 := h866c.2.1
                                          have p866_2 := h866c.2.2.1
                                          have p866_3 := h866c.2.2.2
                                          linarith only [hlam, p866_0]
                                      · rcases h5bigk with h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c | h892c
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc15, hlam, hphi, ht0b, ht5b, p800_1, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, p892_1, u2ehi4]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc35, hlam, hphi, ht0b, ht5b, p800_1, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h2, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p892_1, u2ehi4]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h2, h6, h786, hc01, hc35, hlam, hphi, ht0b, ht5b, p800_1, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h2, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h5, hlam, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h790, hlam, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h2, h6, h786, h790, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h786, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h793, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h797, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h0, h6, h786, hc01, hc45, hlam, hphi, ht0b, ht5b, p800_1, p892_1]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h787, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h794, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h798, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [h799, hlam, p892_0]
                                        · have p892_0 := h892c.1
                                          have p892_1 := h892c.2.1
                                          have p892_2 := h892c.2.2.1
                                          have p892_3 := h892c.2.2.2
                                          linarith only [hlam, p892_0]
                              · linarith only [h4, h830, hlam]
                            · linarith only [h0, h829, hlam, p800_1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            rcases p800_3 (m.d 0 1) (by simp) with h920 | h920
                            · rcases p800_3 (m.d 0 2) (by simp) with h921 | h921
                              · rcases p800_3 (m.d 0 3) (by simp) with h922 | h922
                                · linarith only [h3, h922, hlam]
                                · linarith only [h786, h922, hlam]
                              · linarith only [h5, h921, hlam]
                            · linarith only [h2, h920, hlam]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h1, hlam, p800_1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h3, hlam, p800_1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h6, hlam, p800_1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h2, h6, h790, hc34, hlam, hphi, ht23, p800_1, u2ehi4]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p800_1, u2ehi1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h4, hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h3, h6, hc34, hlam, hphi, ht23, p800_1, u2ehi2]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h2, h6, h790, hc34, hlam, hphi, ht23, p800_1, u2ehi4]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h2, hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h5, hlam, p800_1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h786, hlam, p800_0]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [h787, hlam, p800_1]
                          · have p800_0 := h800c.1
                            have p800_1 := h800c.2.1
                            have p800_2 := h800c.2.2.1
                            have p800_3 := h800c.2.2.2
                            linarith only [hlam, p800_0]
                        · linarith only [h2, h6, h786, h790, h799, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                      · linarith only [h6, h787, h795, h797, h798, hc34, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h6, h786, h797, hc23, hc34, hlam, hphi]
                · linarith only [h6, h786, h787, h789, h794, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h6, h786, h793, hc13, hc34, hlam, hphi]
          · linarith only [h788, h790, hc25, hlam, hphi, u2ehi2]
        · linarith only [h788, h789, hc24, hlam, hphi, u2ehi2]
      · linarith only [h3, h6, h788, hc34, hlam, hphi, ht23, u2ehi1]
    · linarith only [h6, h786, h787, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h951 | h951
    · rcases m.htr 1 2 3 (by decide) (by decide) with h952 | h952
      · rcases m.htr 1 2 4 (by decide) (by decide) with h953 | h953
        · rcases m.htr 1 2 5 (by decide) (by decide) with h954 | h954
          · rcases m.htr 1 3 4 (by decide) (by decide) with h955 | h955
            · linarith only [h1, h6, h955, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h957 | h957
              · linarith only [h1, h786, h957, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h959 | h959
                · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
                  · linarith only [h0, h4, h6, h952, h960, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h962 | h962
                    · linarith only [h1, h786, h952, h962, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h964 | h964
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h965 | h965
                        · rcases h0bigk with h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c | h966c
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p966_1, u2ehi2]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            rcases p966_3 (m.d 0 1) (by simp) with h969 | h969
                            · rcases p966_3 (m.d 0 2) (by simp) with h970 | h970
                              · linarith only [h0, h970, hlam]
                              · linarith only [h3, h970, hlam]
                            · linarith only [h1, h969, hlam]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            rcases p966_3 (m.d 0 1) (by simp) with h974 | h974
                            · rcases p966_3 (m.d 0 2) (by simp) with h975 | h975
                              · linarith only [h0, h975, hlam]
                              · linarith only [h4, h975, hlam]
                            · linarith only [h974, hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            rcases p966_3 (m.d 0 1) (by simp) with h979 | h979
                            · rcases p966_3 (m.d 0 2) (by simp) with h980 | h980
                              · linarith only [h0, h980, hlam]
                              · linarith only [h5, h980, hlam]
                            · linarith only [h2, h979, hlam]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h0, hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            rcases p966_3 (m.d 0 1) (by simp) with h986 | h986
                            · rcases p966_3 (m.d 0 2) (by simp) with h987 | h987
                              · rcases p966_3 (m.d 0 3) (by simp) with h988 | h988
                                · linarith only [h3, h988, hlam]
                                · rcases p966_3 (m.d 0 4) (by simp) with h990 | h990
                                  · linarith only [h4, h990, hlam]
                                  · linarith only [h6, h990, hlam]
                              · linarith only [h3, h987, hlam]
                            · linarith only [h1, h986, hlam]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            rcases p966_3 (m.d 0 1) (by simp) with h995 | h995
                            · rcases p966_3 (m.d 0 2) (by simp) with h996 | h996
                              · rcases p966_3 (m.d 0 3) (by simp) with h997 | h997
                                · linarith only [h3, h997, hlam]
                                · rcases p966_3 (m.d 0 4) (by simp) with h999 | h999
                                  · linarith only [h4, h999, hlam]
                                  · rcases p966_3 (m.d 0 5) (by simp) with h1001 | h1001
                                    · linarith only [h1001, h5, hlam]
                                    · rcases h0emax with h1003 | h1003 | h1003 | h1003 | h1003
                                      · linarith only [h0, h1003, h953, h962, h964, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                      · linarith only [h1003, h2, h951, h952, h957, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p966_1, u2ehi2]
                                      · rcases h5bigk with h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h0, h951, h952, h957, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1006_1, p966_1, u2ehi2]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h0, h951, h962, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1006_1, p966_1, u2ehi2]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h786, hlam, p1006_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h0, h951, hc01, hc45, hlam, hphi, ht0b, ht5b, p1006_1, p966_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h2, hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h959, h962, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1006_1, u2ehi2]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h957, hlam, p1006_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h0, h2, h951, hc01, hc45, hlam, hphi, ht0b, ht5b, p1006_1, p966_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h5, hlam, p1006_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h954, hlam, p1006_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h962, hlam, p1006_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h953, h964, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1006_1]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h5, h965, hc34, hlam, hphi, ht23, p1006_1, u2ehi4]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h954, h965, hc34, hlam, hphi, ht23, p1006_1, u2ehi4]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h965, hc34, hlam, hphi, ht23, p1006_1, u2ehi4]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          rcases p1006_3 (m.d 0 5) (by simp) with h1026 | h1026
                                          · linarith only [h1026, h786, hlam]
                                          · linarith only [h1026, h951, hlam]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h951, hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h959, hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h964, hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [h965, hlam, p1006_0]
                                        · have p1006_0 := h1006c.1
                                          have p1006_1 := h1006c.2.1
                                          have p1006_2 := h1006c.2.2.1
                                          have p1006_3 := h1006c.2.2.2
                                          linarith only [hlam, p1006_0]
                                      · rcases h5bigk with h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c | h1034c
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h0, h951, h952, h957, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1034_1, p966_1, u2ehi2]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h0, h951, h962, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1034_1, p966_1, u2ehi2]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h786, hlam, p1034_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h0, h951, hc01, hc45, hlam, hphi, ht0b, ht5b, p1034_1, p966_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h2, hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h962, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1034_1, u2ehi2]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h957, hlam, p1034_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h0, h2, h951, hc01, hc45, hlam, hphi, ht0b, ht5b, p1034_1, p966_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h5, hlam, p1034_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h954, hlam, p1034_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h962, hlam, p1034_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h953, h964, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1034_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h786, h965, hc03, hc34, hlam, hphi, p1034_1]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h954, h965, hc34, hlam, hphi, ht23, p1034_1, u2ehi4]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h965, hc34, hlam, hphi, ht23, p1034_1, u2ehi4]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          rcases p1034_3 (m.d 0 5) (by simp) with h1054 | h1054
                                          · linarith only [h1054, h786, hlam]
                                          · linarith only [h1054, h951, hlam]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h951, hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h959, hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h964, hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [h965, hlam, p1034_0]
                                        · have p1034_0 := h1034c.1
                                          have p1034_1 := h1034c.2.1
                                          have p1034_2 := h1034c.2.2.1
                                          have p1034_3 := h1034c.2.2.2
                                          linarith only [hlam, p1034_0]
                                      · rcases h5bigk with h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c | h1062c
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h952, h957, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1062_1, u2ehi2]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h0, h5, h962, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1062_1, u2ehi2]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h786, hlam, p1062_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h0, h951, hc01, hc45, hlam, hphi, ht0b, ht5b, p1062_1, p966_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h2, hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h962, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1062_1, u2ehi2]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h957, hlam, p1062_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h0, h2, h951, hc01, hc45, hlam, hphi, ht0b, ht5b, p1062_1, p966_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h5, hlam, p1062_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h954, hlam, p1062_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h962, hlam, p1062_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1062_1]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h5, h965, hc34, hlam, hphi, ht23, p1062_1, u2ehi4]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h954, h965, hc34, hlam, hphi, ht23, p1062_1, u2ehi4]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h965, hc34, hlam, hphi, ht23, p1062_1, u2ehi4]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          rcases p1062_3 (m.d 0 5) (by simp) with h1082 | h1082
                                          · linarith only [h1082, h786, hlam]
                                          · linarith only [h1082, h951, hlam]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h951, hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h959, hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h964, hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [h965, hlam, p1062_0]
                                        · have p1062_0 := h1062c.1
                                          have p1062_1 := h1062c.2.1
                                          have p1062_2 := h1062c.2.2.1
                                          have p1062_3 := h1062c.2.2.2
                                          linarith only [hlam, p1062_0]
                              · linarith only [h4, h996, hlam]
                            · linarith only [h0, h995, hlam, p966_1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            rcases p966_3 (m.d 0 1) (by simp) with h1092 | h1092
                            · rcases p966_3 (m.d 0 2) (by simp) with h1093 | h1093
                              · rcases p966_3 (m.d 0 3) (by simp) with h1094 | h1094
                                · linarith only [h1094, h3, hlam]
                                · rcases p966_3 (m.d 0 4) (by simp) with h1096 | h1096
                                  · linarith only [h1096, h4, hlam]
                                  · linarith only [h1096, h951, hlam]
                              · linarith only [h1093, h5, hlam]
                            · linarith only [h1092, h2, hlam]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h1, hlam, p966_1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h3, hlam, p966_1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h6, hlam, p966_1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h786, hlam, p966_1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p966_1, u2ehi1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h4, hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h1, h6, h952, hc34, hlam, hphi, ht23, p966_1, u2ehi2]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h1, h6, h786, h952, hc34, hlam, hphi, ht23, p966_1, u2ehi2]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h2, hlam, p966_0]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h5, hlam, p966_1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h1, h786, h952, h965, hc34, hlam, hphi, ht23, p966_1, u2ehi2]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [h951, hlam, p966_1]
                          · have p966_0 := h966c.1
                            have p966_1 := h966c.2.1
                            have p966_2 := h966c.2.2.1
                            have p966_3 := h966c.2.2.2
                            linarith only [hlam, p966_0]
                        · linarith only [h1, h6, h952, h965, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h6, h951, h964, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h6, h951, h953, h959, hc34, hlam, hphi, ht23, u2ehi3]
          · linarith only [h0, h5, h952, h954, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
        · linarith only [h952, h953, hc24, hlam, hphi, u2ehi2]
      · linarith only [h3, h6, h952, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1123 | h1123
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1124 | h1124
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1125 | h1125
            · linarith only [h1, h1125, h6, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1127 | h1127
              · linarith only [h1, h1127, h786, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1129 | h1129
                · linarith only [h0, h1, h1122, h1123, h1129, h6, h951, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                  · linarith only [h1, h1122, h1131, h6, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                    · linarith only [h1, h1122, h1133, h786, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1135 | h1135
                      · linarith only [h1, h1122, h1135, h6, h951, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1137 | h1137
                        · linarith only [h1, h1122, h1137, h6, h951, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1, h1122, h1137, h6, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h1122, h1124, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
        · linarith only [h1122, h1123, hc24, hlam, hphi, u2ehi2]
      · linarith only [h1122, h3, h6, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5 h6
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5 h6

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 10690000 in
set_option maxHeartbeats 10690000 in
theorem r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3 h4
  · exact r1l7_10_12_25_L_I_L_R_H_I_x0_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3 h4

end R2N4
