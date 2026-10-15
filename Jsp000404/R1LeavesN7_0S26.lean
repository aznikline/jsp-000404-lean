import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S25

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14163 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h14165 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h14167 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 2 3 4 (by decide) (by decide) with h14603 | h14603
  · linarith only [h14159, h14160, h14163, h14167, h14603, h7, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h14605 | h14605
    · linarith only [h1, h13284, h14160, h14605, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h14607 | h14607
      · linarith only [h0, h14161, h14167, h14607, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h14609 | h14609
        · rcases h1bigk with h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c | h14610c
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            rcases p14610_3 (m.d 0 1) (by simp) with h14612 | h14612
            · rcases p14610_3 (m.d 1 2) (by simp) with h14613 | h14613
              · linarith only [h14613, hlam, p14610_0]
              · rcases p14610_3 (m.d 1 3) (by simp) with h14615 | h14615
                · linarith only [h1, h14615, hlam]
                · rcases p14610_3 (m.d 1 4) (by simp) with h14617 | h14617
                  · linarith only [h14617, h2, hlam]
                  · rcases p14610_3 (m.d 1 5) (by simp) with h14619 | h14619
                    · linarith only [h14619, h3, hlam]
                    · rcases h1emax with h14621 | h14621 | h14621 | h14621 | h14621
                      · linarith only [h14621, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p14610_1]
                      · rcases h2bigk with h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c | h14623c
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          rcases p14623_3 (m.d 0 2) (by simp) with h14625 | h14625
                          · rcases p14623_3 (m.d 1 2) (by simp) with h14626 | h14626
                            · linarith only [h0, h14626, hlam]
                            · rcases p14623_3 (m.d 2 3) (by simp) with h14628 | h14628
                              · linarith only [h14628, h4, hlam]
                              · rcases p14623_3 (m.d 2 4) (by simp) with h14630 | h14630
                                · linarith only [h14630, h5, hlam]
                                · rcases p14623_3 (m.d 2 5) (by simp) with h14632 | h14632
                                  · linarith only [h14632, h6, hlam]
                                  · rcases h4bigk with h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c | h14634c
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      rcases p14634_3 (m.d 0 4) (by simp) with h14636 | h14636
                                      · rcases p14634_3 (m.d 1 4) (by simp) with h14637 | h14637
                                        · linarith only [h14637, h2, hlam]
                                        · rcases p14634_3 (m.d 2 4) (by simp) with h14639 | h14639
                                          · linarith only [h14639, h5, hlam]
                                          · rcases p14634_3 (m.d 3 4) (by simp) with h14641 | h14641
                                            · rcases p14634_3 (m.d 4 5) (by simp) with h14642 | h14642
                                              · linarith only [h14159, h14642, hlam]
                                              · linarith only [h14167, h14642, hlam]
                                            · linarith only [h14163, h14641, hlam]
                                      · linarith only [h14636, h2, hlam]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      rcases p14634_3 (m.d 0 4) (by simp) with h14647 | h14647
                                      · rcases p14634_3 (m.d 1 4) (by simp) with h14648 | h14648
                                        · linarith only [h14648, h2, hlam]
                                        · linarith only [h14161, h14648, hlam]
                                      · linarith only [h14647, h5, hlam]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h7, hlam, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14160, h14163, h14167, h7, hc23, hc34, hlam, hphi, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h2, hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h13284, h14159, h14167, h14603, hc23, hc35, hlam, hphi, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14163, hlam, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14167, hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h5, hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14161, hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14603, hlam, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14607, hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14159, h14167, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      rcases p14634_3 (m.d 0 4) (by simp) with h14665 | h14665
                                      · linarith only [h14665, h7, hlam]
                                      · linarith only [h14665, h2, hlam]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      rcases p14634_3 (m.d 0 4) (by simp) with h14668 | h14668
                                      · linarith only [h14668, h7, hlam]
                                      · linarith only [h14668, h5, hlam]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14161, h14167, h14603, hc23, hc34, hlam, hphi, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14159, hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14159, h14161, h14603, h7, hc23, hc34, hlam, hphi, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14159, h14603, h7, hc23, hc34, hlam, hphi, p14634_1]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [h14609, hlam, p14634_0]
                                    · have p14634_0 := h14634c.1
                                      have p14634_1 := h14634c.2.1
                                      have p14634_2 := h14634c.2.2.1
                                      have p14634_3 := h14634c.2.2.2
                                      linarith only [hlam, p14634_0]
                          · linarith only [h0, h14625, hlam]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          rcases p14623_3 (m.d 0 2) (by simp) with h14679 | h14679
                          · rcases p14623_3 (m.d 1 2) (by simp) with h14680 | h14680
                            · linarith only [h0, h14680, hlam]
                            · linarith only [h14160, h14680, hlam]
                          · linarith only [h14679, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          rcases p14623_3 (m.d 0 2) (by simp) with h14684 | h14684
                          · rcases p14623_3 (m.d 1 2) (by simp) with h14685 | h14685
                            · linarith only [h0, h14685, hlam]
                            · linarith only [h14161, h14685, hlam]
                          · linarith only [h14684, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          rcases p14623_3 (m.d 0 2) (by simp) with h14689 | h14689
                          · rcases p14623_3 (m.d 1 2) (by simp) with h14690 | h14690
                            · linarith only [h0, h14690, hlam]
                            · linarith only [h14162, h14690, hlam]
                          · linarith only [h14689, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h0, hlam, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14621, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14603, h14621, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14603, h14607, h14621, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h4, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14160, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14603, hlam, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14605, hlam, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h5, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14161, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14161, h14621, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14607, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h6, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14162, hlam, p14623_0]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14162, h14621, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [h14162, h14621, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14623_1]
                        · have p14623_0 := h14623c.1
                          have p14623_1 := h14623c.2.1
                          have p14623_2 := h14623c.2.2.1
                          have p14623_3 := h14623c.2.2.2
                          linarith only [hlam, p14623_0]
                      · rcases h2bigk with h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c | h14714c
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          rcases p14714_3 (m.d 0 2) (by simp) with h14716 | h14716
                          · rcases p14714_3 (m.d 1 2) (by simp) with h14717 | h14717
                            · linarith only [h0, h14717, hlam]
                            · rcases p14714_3 (m.d 2 3) (by simp) with h14719 | h14719
                              · linarith only [h14719, h4, hlam]
                              · rcases p14714_3 (m.d 2 4) (by simp) with h14721 | h14721
                                · linarith only [h14721, h5, hlam]
                                · rcases p14714_3 (m.d 2 5) (by simp) with h14723 | h14723
                                  · linarith only [h14723, h6, hlam]
                                  · rcases h4bigk with h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c | h14725c
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      rcases p14725_3 (m.d 0 4) (by simp) with h14727 | h14727
                                      · rcases p14725_3 (m.d 1 4) (by simp) with h14728 | h14728
                                        · linarith only [h14728, h2, hlam]
                                        · rcases p14725_3 (m.d 2 4) (by simp) with h14730 | h14730
                                          · linarith only [h14730, h5, hlam]
                                          · rcases p14725_3 (m.d 3 4) (by simp) with h14732 | h14732
                                            · rcases p14725_3 (m.d 4 5) (by simp) with h14733 | h14733
                                              · linarith only [h14159, h14733, hlam]
                                              · linarith only [h14167, h14733, hlam]
                                            · linarith only [h14163, h14732, hlam]
                                      · linarith only [h14727, h2, hlam]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      rcases p14725_3 (m.d 0 4) (by simp) with h14738 | h14738
                                      · rcases p14725_3 (m.d 1 4) (by simp) with h14739 | h14739
                                        · linarith only [h14739, h2, hlam]
                                        · linarith only [h14161, h14739, hlam]
                                      · linarith only [h14738, h5, hlam]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h7, hlam, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14160, h14163, h14167, h7, hc23, hc34, hlam, hphi, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h2, hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h0, h14161, h14603, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14714_1, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14163, hlam, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14167, hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h5, hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14161, hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14603, hlam, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14607, hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14159, h14167, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      rcases p14725_3 (m.d 0 4) (by simp) with h14756 | h14756
                                      · linarith only [h14756, h7, hlam]
                                      · linarith only [h14756, h2, hlam]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      rcases p14725_3 (m.d 0 4) (by simp) with h14759 | h14759
                                      · linarith only [h14759, h7, hlam]
                                      · linarith only [h14759, h5, hlam]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14161, h14167, h14603, hc23, hc34, hlam, hphi, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14159, hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14159, h14161, h14603, h7, hc23, hc34, hlam, hphi, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14159, h14603, h7, hc23, hc34, hlam, hphi, p14725_1]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [h14609, hlam, p14725_0]
                                    · have p14725_0 := h14725c.1
                                      have p14725_1 := h14725c.2.1
                                      have p14725_2 := h14725c.2.2.1
                                      have p14725_3 := h14725c.2.2.2
                                      linarith only [hlam, p14725_0]
                          · linarith only [h0, h14716, hlam]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          rcases p14714_3 (m.d 0 2) (by simp) with h14770 | h14770
                          · rcases p14714_3 (m.d 1 2) (by simp) with h14771 | h14771
                            · linarith only [h0, h14771, hlam]
                            · linarith only [h14160, h14771, hlam]
                          · linarith only [h14770, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          rcases p14714_3 (m.d 0 2) (by simp) with h14775 | h14775
                          · rcases p14714_3 (m.d 1 2) (by simp) with h14776 | h14776
                            · linarith only [h0, h14776, hlam]
                            · linarith only [h14161, h14776, hlam]
                          · linarith only [h14775, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          rcases p14714_3 (m.d 0 2) (by simp) with h14780 | h14780
                          · rcases p14714_3 (m.d 1 2) (by simp) with h14781 | h14781
                            · linarith only [h0, h14781, hlam]
                            · linarith only [h14162, h14781, hlam]
                          · linarith only [h14780, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h0, hlam, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14603, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14603, h14607, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h4, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14160, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14603, hlam, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14605, hlam, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h5, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14161, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14607, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h6, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14162, hlam, p14714_0]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [h14162, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p14714_1]
                        · have p14714_0 := h14714c.1
                          have p14714_1 := h14714c.2.1
                          have p14714_2 := h14714c.2.2.1
                          have p14714_3 := h14714c.2.2.2
                          linarith only [hlam, p14714_0]
                      · rcases h2bigk with h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c | h14805c
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          rcases p14805_3 (m.d 0 2) (by simp) with h14807 | h14807
                          · rcases p14805_3 (m.d 1 2) (by simp) with h14808 | h14808
                            · linarith only [h0, h14808, hlam]
                            · rcases p14805_3 (m.d 2 3) (by simp) with h14810 | h14810
                              · linarith only [h14810, h4, hlam]
                              · rcases p14805_3 (m.d 2 4) (by simp) with h14812 | h14812
                                · linarith only [h14812, h5, hlam]
                                · rcases p14805_3 (m.d 2 5) (by simp) with h14814 | h14814
                                  · linarith only [h14814, h6, hlam]
                                  · rcases h4bigk with h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c | h14816c
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      rcases p14816_3 (m.d 0 4) (by simp) with h14818 | h14818
                                      · rcases p14816_3 (m.d 1 4) (by simp) with h14819 | h14819
                                        · linarith only [h14819, h2, hlam]
                                        · rcases p14816_3 (m.d 2 4) (by simp) with h14821 | h14821
                                          · linarith only [h14821, h5, hlam]
                                          · rcases p14816_3 (m.d 3 4) (by simp) with h14823 | h14823
                                            · rcases p14816_3 (m.d 4 5) (by simp) with h14824 | h14824
                                              · linarith only [h14159, h14824, hlam]
                                              · linarith only [h14167, h14824, hlam]
                                            · linarith only [h14163, h14823, hlam]
                                      · linarith only [h14818, h2, hlam]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      rcases p14816_3 (m.d 0 4) (by simp) with h14829 | h14829
                                      · rcases p14816_3 (m.d 1 4) (by simp) with h14830 | h14830
                                        · linarith only [h14830, h2, hlam]
                                        · linarith only [h14161, h14830, hlam]
                                      · linarith only [h14829, h5, hlam]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h7, hlam, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14160, h14163, h14167, h7, hc23, hc34, hlam, hphi, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h2, hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h0, h14161, h14603, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14805_1, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14163, hlam, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14167, hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h5, hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14161, hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14603, hlam, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14607, hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14159, h14167, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      rcases p14816_3 (m.d 0 4) (by simp) with h14847 | h14847
                                      · linarith only [h14847, h7, hlam]
                                      · linarith only [h14847, h2, hlam]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      rcases p14816_3 (m.d 0 4) (by simp) with h14850 | h14850
                                      · linarith only [h14850, h7, hlam]
                                      · linarith only [h14850, h5, hlam]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14161, h14167, h14603, hc23, hc34, hlam, hphi, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14159, hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14159, h14161, h14603, h7, hc23, hc34, hlam, hphi, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14159, h14603, h7, hc23, hc34, hlam, hphi, p14816_1]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [h14609, hlam, p14816_0]
                                    · have p14816_0 := h14816c.1
                                      have p14816_1 := h14816c.2.1
                                      have p14816_2 := h14816c.2.2.1
                                      have p14816_3 := h14816c.2.2.2
                                      linarith only [hlam, p14816_0]
                          · linarith only [h0, h14807, hlam]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          rcases p14805_3 (m.d 0 2) (by simp) with h14861 | h14861
                          · rcases p14805_3 (m.d 1 2) (by simp) with h14862 | h14862
                            · linarith only [h0, h14862, hlam]
                            · linarith only [h14160, h14862, hlam]
                          · linarith only [h14861, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          rcases p14805_3 (m.d 0 2) (by simp) with h14866 | h14866
                          · rcases p14805_3 (m.d 1 2) (by simp) with h14867 | h14867
                            · linarith only [h0, h14867, hlam]
                            · linarith only [h14161, h14867, hlam]
                          · linarith only [h14866, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          rcases p14805_3 (m.d 0 2) (by simp) with h14871 | h14871
                          · rcases p14805_3 (m.d 1 2) (by simp) with h14872 | h14872
                            · linarith only [h0, h14872, hlam]
                            · linarith only [h14162, h14872, hlam]
                          · linarith only [h14871, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h0, hlam, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14603, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14603, h14607, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h4, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14160, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14603, hlam, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14605, hlam, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h5, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14161, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14607, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h6, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14162, hlam, p14805_0]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [h14162, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p14805_1]
                        · have p14805_0 := h14805c.1
                          have p14805_1 := h14805c.2.1
                          have p14805_2 := h14805c.2.2.1
                          have p14805_3 := h14805c.2.2.2
                          linarith only [hlam, p14805_0]
                      · rcases h2bigk with h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c | h14896c
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          rcases p14896_3 (m.d 0 2) (by simp) with h14898 | h14898
                          · rcases p14896_3 (m.d 1 2) (by simp) with h14899 | h14899
                            · linarith only [h0, h14899, hlam]
                            · rcases p14896_3 (m.d 2 3) (by simp) with h14901 | h14901
                              · linarith only [h14901, h4, hlam]
                              · rcases p14896_3 (m.d 2 4) (by simp) with h14903 | h14903
                                · linarith only [h14903, h5, hlam]
                                · rcases p14896_3 (m.d 2 5) (by simp) with h14905 | h14905
                                  · linarith only [h14905, h6, hlam]
                                  · rcases h4bigk with h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c | h14907c
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      rcases p14907_3 (m.d 0 4) (by simp) with h14909 | h14909
                                      · rcases p14907_3 (m.d 1 4) (by simp) with h14910 | h14910
                                        · linarith only [h14910, h2, hlam]
                                        · rcases p14907_3 (m.d 2 4) (by simp) with h14912 | h14912
                                          · linarith only [h14912, h5, hlam]
                                          · rcases p14907_3 (m.d 3 4) (by simp) with h14914 | h14914
                                            · rcases p14907_3 (m.d 4 5) (by simp) with h14915 | h14915
                                              · linarith only [h14159, h14915, hlam]
                                              · linarith only [h14167, h14915, hlam]
                                            · linarith only [h14163, h14914, hlam]
                                      · linarith only [h14909, h2, hlam]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      rcases p14907_3 (m.d 0 4) (by simp) with h14920 | h14920
                                      · rcases p14907_3 (m.d 1 4) (by simp) with h14921 | h14921
                                        · linarith only [h14921, h2, hlam]
                                        · linarith only [h14161, h14921, hlam]
                                      · linarith only [h14920, h5, hlam]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h7, hlam, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14160, h14163, h14167, h7, hc23, hc34, hlam, hphi, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h2, hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h0, h14161, h14603, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14896_1, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14163, hlam, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14167, hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h5, hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14161, hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14603, hlam, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14607, hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14159, h14167, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      rcases p14907_3 (m.d 0 4) (by simp) with h14938 | h14938
                                      · linarith only [h14938, h7, hlam]
                                      · linarith only [h14938, h2, hlam]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      rcases p14907_3 (m.d 0 4) (by simp) with h14941 | h14941
                                      · linarith only [h14941, h7, hlam]
                                      · linarith only [h14941, h5, hlam]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14161, h14167, h14603, hc23, hc34, hlam, hphi, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14159, hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14159, h14161, h14603, h7, hc23, hc34, hlam, hphi, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14159, h14603, h7, hc23, hc34, hlam, hphi, p14907_1]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [h14609, hlam, p14907_0]
                                    · have p14907_0 := h14907c.1
                                      have p14907_1 := h14907c.2.1
                                      have p14907_2 := h14907c.2.2.1
                                      have p14907_3 := h14907c.2.2.2
                                      linarith only [hlam, p14907_0]
                          · linarith only [h0, h14898, hlam]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          rcases p14896_3 (m.d 0 2) (by simp) with h14952 | h14952
                          · rcases p14896_3 (m.d 1 2) (by simp) with h14953 | h14953
                            · linarith only [h0, h14953, hlam]
                            · linarith only [h14160, h14953, hlam]
                          · linarith only [h14952, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          rcases p14896_3 (m.d 0 2) (by simp) with h14957 | h14957
                          · rcases p14896_3 (m.d 1 2) (by simp) with h14958 | h14958
                            · linarith only [h0, h14958, hlam]
                            · linarith only [h14161, h14958, hlam]
                          · linarith only [h14957, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          rcases p14896_3 (m.d 0 2) (by simp) with h14962 | h14962
                          · rcases p14896_3 (m.d 1 2) (by simp) with h14963 | h14963
                            · linarith only [h0, h14963, hlam]
                            · linarith only [h14162, h14963, hlam]
                          · linarith only [h14962, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h0, hlam, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14603, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14603, h14607, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h4, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14160, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14603, hlam, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14605, hlam, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h5, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14161, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14161, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14607, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h6, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14162, hlam, p14896_0]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [h14162, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p14896_1]
                        · have p14896_0 := h14896c.1
                          have p14896_1 := h14896c.2.1
                          have p14896_2 := h14896c.2.2.1
                          have p14896_3 := h14896c.2.2.2
                          linarith only [hlam, p14896_0]
            · linarith only [h14612, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            rcases p14610_3 (m.d 0 1) (by simp) with h14988 | h14988
            · rcases p14610_3 (m.d 1 2) (by simp) with h14989 | h14989
              · linarith only [h0, h14989, hlam]
              · linarith only [h14160, h14989, hlam]
            · linarith only [h14988, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            rcases p14610_3 (m.d 0 1) (by simp) with h14993 | h14993
            · rcases p14610_3 (m.d 1 2) (by simp) with h14994 | h14994
              · linarith only [h0, h14994, hlam]
              · linarith only [h14161, h14994, hlam]
            · linarith only [h14993, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            rcases p14610_3 (m.d 0 1) (by simp) with h14998 | h14998
            · rcases p14610_3 (m.d 1 2) (by simp) with h14999 | h14999
              · linarith only [h0, h14999, hlam]
              · linarith only [h14162, h14999, hlam]
            · linarith only [h14998, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h0, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            rcases p14610_3 (m.d 0 1) (by simp) with h15005 | h15005
            · rcases p14610_3 (m.d 1 2) (by simp) with h15006 | h15006
              · rcases p14610_3 (m.d 1 3) (by simp) with h15007 | h15007
                · linarith only [h14160, h15007, hlam]
                · rcases p14610_3 (m.d 1 4) (by simp) with h15009 | h15009
                  · linarith only [h14161, h15009, hlam]
                  · linarith only [h14163, h15009, hlam]
              · linarith only [h14160, h15006, hlam]
            · linarith only [h1, h15005, hlam]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            rcases p14610_3 (m.d 0 1) (by simp) with h15014 | h15014
            · rcases p14610_3 (m.d 1 2) (by simp) with h15015 | h15015
              · rcases p14610_3 (m.d 1 3) (by simp) with h15016 | h15016
                · linarith only [h14160, h15016, hlam]
                · rcases p14610_3 (m.d 1 4) (by simp) with h15018 | h15018
                  · linarith only [h14161, h15018, hlam]
                  · rcases p14610_3 (m.d 1 5) (by simp) with h15020 | h15020
                    · linarith only [h14162, h15020, hlam]
                    · linarith only [h14167, h15020, hlam]
              · linarith only [h14161, h15015, hlam]
            · linarith only [h15014, h2, hlam]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            rcases p14610_3 (m.d 0 1) (by simp) with h15025 | h15025
            · rcases p14610_3 (m.d 1 2) (by simp) with h15026 | h15026
              · rcases p14610_3 (m.d 1 3) (by simp) with h15027 | h15027
                · linarith only [h14160, h15027, hlam]
                · rcases p14610_3 (m.d 1 4) (by simp) with h15029 | h15029
                  · linarith only [h14161, h15029, hlam]
                  · rcases p14610_3 (m.d 1 5) (by simp) with h15031 | h15031
                    · linarith only [h14162, h15031, hlam]
                    · rcases h1emax with h15033 | h15033 | h15033 | h15033 | h15033
                      · linarith only [h0, h14163, h14167, h15033, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14610_1]
                      · linarith only [h14160, h14163, h14167, h15033, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14610_1]
                      · rcases h2bigk with h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c | h15036c
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h14160, h14163, h14167, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p15036_1]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          rcases p15036_3 (m.d 0 2) (by simp) with h15039 | h15039
                          · rcases p15036_3 (m.d 1 2) (by simp) with h15040 | h15040
                            · linarith only [h0, h15040, hlam]
                            · linarith only [h14160, h15040, hlam]
                          · linarith only [h15039, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          rcases p15036_3 (m.d 0 2) (by simp) with h15044 | h15044
                          · rcases p15036_3 (m.d 1 2) (by simp) with h15045 | h15045
                            · linarith only [h0, h15045, hlam]
                            · linarith only [h14161, h15045, hlam]
                          · linarith only [h15044, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          rcases p15036_3 (m.d 0 2) (by simp) with h15049 | h15049
                          · rcases p15036_3 (m.d 1 2) (by simp) with h15050 | h15050
                            · linarith only [h0, h15050, hlam]
                            · linarith only [h14162, h15050, hlam]
                          · linarith only [h15049, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h0, hlam, p15036_1]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          rcases p15036_3 (m.d 0 2) (by simp) with h15056 | h15056
                          · rcases p15036_3 (m.d 1 2) (by simp) with h15057 | h15057
                            · rcases p15036_3 (m.d 2 3) (by simp) with h15058 | h15058
                              · linarith only [h15058, hlam, p15036_0]
                              · rcases p15036_3 (m.d 2 4) (by simp) with h15060 | h15060
                                · linarith only [h14161, h15060, hlam]
                                · linarith only [h14603, h15060, hlam]
                            · linarith only [h15057, hlam, p15036_0]
                          · linarith only [h15056, h4, hlam]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          rcases p15036_3 (m.d 0 2) (by simp) with h15065 | h15065
                          · rcases p15036_3 (m.d 1 2) (by simp) with h15066 | h15066
                            · rcases p15036_3 (m.d 2 3) (by simp) with h15067 | h15067
                              · linarith only [h14160, h15067, hlam]
                              · rcases p15036_3 (m.d 2 4) (by simp) with h15069 | h15069
                                · linarith only [h15069, hlam, p15036_0]
                                · rcases p15036_3 (m.d 2 5) (by simp) with h15071 | h15071
                                  · linarith only [h14162, h15071, hlam]
                                  · linarith only [h14607, h15071, hlam]
                            · linarith only [h15066, hlam, p15036_0]
                          · linarith only [h15065, h5, hlam]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          rcases p15036_3 (m.d 0 2) (by simp) with h15076 | h15076
                          · rcases p15036_3 (m.d 1 2) (by simp) with h15077 | h15077
                            · rcases p15036_3 (m.d 2 3) (by simp) with h15078 | h15078
                              · linarith only [h14160, h15078, hlam]
                              · rcases p15036_3 (m.d 2 4) (by simp) with h15080 | h15080
                                · linarith only [h14161, h15080, hlam]
                                · rcases p15036_3 (m.d 2 5) (by simp) with h15082 | h15082
                                  · linarith only [h15082, hlam, p15036_0]
                                  · rcases h4bigk with h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c | h15084c
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      rcases p15084_3 (m.d 0 4) (by simp) with h15086 | h15086
                                      · rcases p15084_3 (m.d 1 4) (by simp) with h15087 | h15087
                                        · linarith only [h15087, h2, hlam]
                                        · rcases p15084_3 (m.d 2 4) (by simp) with h15089 | h15089
                                          · linarith only [h15089, h5, hlam]
                                          · rcases p15084_3 (m.d 3 4) (by simp) with h15091 | h15091
                                            · rcases p15084_3 (m.d 4 5) (by simp) with h15092 | h15092
                                              · linarith only [h14159, h15092, hlam]
                                              · linarith only [h14167, h15092, hlam]
                                            · linarith only [h14163, h15091, hlam]
                                      · linarith only [h15086, h2, hlam]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      rcases p15084_3 (m.d 0 4) (by simp) with h15097 | h15097
                                      · rcases p15084_3 (m.d 1 4) (by simp) with h15098 | h15098
                                        · linarith only [h15098, h2, hlam]
                                        · linarith only [h14161, h15098, hlam]
                                      · linarith only [h15097, h5, hlam]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h7, hlam, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14160, h14163, h14167, h7, hc23, hc34, hlam, hphi, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h2, hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14167, h14603, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14610_1, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14163, hlam, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14167, hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h5, hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14161, hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14603, hlam, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14607, hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14159, h14167, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      rcases p15084_3 (m.d 0 4) (by simp) with h15115 | h15115
                                      · linarith only [h15115, h7, hlam]
                                      · linarith only [h15115, h2, hlam]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      rcases p15084_3 (m.d 0 4) (by simp) with h15118 | h15118
                                      · linarith only [h15118, h7, hlam]
                                      · linarith only [h15118, h5, hlam]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14161, h14167, h14603, hc23, hc34, hlam, hphi, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14159, hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14159, h14161, h14603, h7, hc23, hc34, hlam, hphi, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14159, h14603, h7, hc23, hc34, hlam, hphi, p15084_1]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [h14609, hlam, p15084_0]
                                    · have p15084_0 := h15084c.1
                                      have p15084_1 := h15084c.2.1
                                      have p15084_2 := h15084c.2.2.1
                                      have p15084_3 := h15084c.2.2.2
                                      linarith only [hlam, p15084_0]
                            · linarith only [h15077, hlam, p15036_0]
                          · linarith only [h15076, h6, hlam]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h4, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h14160, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h14603, hlam, p15036_1]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h14605, hlam, p15036_1]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h5, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h14161, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h0, h14161, h14167, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p15036_1]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h14607, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h6, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h14162, hlam, p15036_0]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h0, h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p15036_1]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [h0, h14162, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p15036_1]
                        · have p15036_0 := h15036c.1
                          have p15036_1 := h15036c.2.1
                          have p15036_2 := h15036c.2.2.1
                          have p15036_3 := h15036c.2.2.2
                          linarith only [hlam, p15036_0]
                      · rcases h2bigk with h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c | h15145c
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h14167, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p15145_1]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          rcases p15145_3 (m.d 0 2) (by simp) with h15148 | h15148
                          · rcases p15145_3 (m.d 1 2) (by simp) with h15149 | h15149
                            · linarith only [h0, h15149, hlam]
                            · linarith only [h14160, h15149, hlam]
                          · linarith only [h15148, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          rcases p15145_3 (m.d 0 2) (by simp) with h15153 | h15153
                          · rcases p15145_3 (m.d 1 2) (by simp) with h15154 | h15154
                            · linarith only [h0, h15154, hlam]
                            · linarith only [h14161, h15154, hlam]
                          · linarith only [h15153, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          rcases p15145_3 (m.d 0 2) (by simp) with h15158 | h15158
                          · rcases p15145_3 (m.d 1 2) (by simp) with h15159 | h15159
                            · linarith only [h0, h15159, hlam]
                            · linarith only [h14162, h15159, hlam]
                          · linarith only [h15158, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h0, hlam, p15145_1]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          rcases p15145_3 (m.d 0 2) (by simp) with h15165 | h15165
                          · rcases p15145_3 (m.d 1 2) (by simp) with h15166 | h15166
                            · rcases p15145_3 (m.d 2 3) (by simp) with h15167 | h15167
                              · linarith only [h15167, hlam, p15145_0]
                              · rcases p15145_3 (m.d 2 4) (by simp) with h15169 | h15169
                                · linarith only [h14161, h15169, hlam]
                                · linarith only [h14603, h15169, hlam]
                            · linarith only [h15166, hlam, p15145_0]
                          · linarith only [h15165, h4, hlam]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          rcases p15145_3 (m.d 0 2) (by simp) with h15174 | h15174
                          · rcases p15145_3 (m.d 1 2) (by simp) with h15175 | h15175
                            · rcases p15145_3 (m.d 2 3) (by simp) with h15176 | h15176
                              · linarith only [h14160, h15176, hlam]
                              · rcases p15145_3 (m.d 2 4) (by simp) with h15178 | h15178
                                · linarith only [h15178, hlam, p15145_0]
                                · rcases p15145_3 (m.d 2 5) (by simp) with h15180 | h15180
                                  · linarith only [h14162, h15180, hlam]
                                  · linarith only [h14607, h15180, hlam]
                            · linarith only [h15175, hlam, p15145_0]
                          · linarith only [h15174, h5, hlam]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          rcases p15145_3 (m.d 0 2) (by simp) with h15185 | h15185
                          · rcases p15145_3 (m.d 1 2) (by simp) with h15186 | h15186
                            · rcases p15145_3 (m.d 2 3) (by simp) with h15187 | h15187
                              · linarith only [h14160, h15187, hlam]
                              · rcases p15145_3 (m.d 2 4) (by simp) with h15189 | h15189
                                · linarith only [h14161, h15189, hlam]
                                · rcases p15145_3 (m.d 2 5) (by simp) with h15191 | h15191
                                  · linarith only [h15191, hlam, p15145_0]
                                  · rcases h4bigk with h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c | h15193c
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      rcases p15193_3 (m.d 0 4) (by simp) with h15195 | h15195
                                      · rcases p15193_3 (m.d 1 4) (by simp) with h15196 | h15196
                                        · linarith only [h15196, h2, hlam]
                                        · rcases p15193_3 (m.d 2 4) (by simp) with h15198 | h15198
                                          · linarith only [h15198, h5, hlam]
                                          · rcases p15193_3 (m.d 3 4) (by simp) with h15200 | h15200
                                            · rcases p15193_3 (m.d 4 5) (by simp) with h15201 | h15201
                                              · linarith only [h14159, h15201, hlam]
                                              · linarith only [h14167, h15201, hlam]
                                            · linarith only [h14163, h15200, hlam]
                                      · linarith only [h15195, h2, hlam]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      rcases p15193_3 (m.d 0 4) (by simp) with h15206 | h15206
                                      · rcases p15193_3 (m.d 1 4) (by simp) with h15207 | h15207
                                        · linarith only [h15207, h2, hlam]
                                        · linarith only [h14161, h15207, hlam]
                                      · linarith only [h15206, h5, hlam]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h7, hlam, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14161, h14167, h14603, h7, hc23, hc34, hlam, hphi, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h2, hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14167, h14603, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14610_1, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14163, hlam, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14167, hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h5, hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14161, hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14603, hlam, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14607, hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14159, h14167, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      rcases p15193_3 (m.d 0 4) (by simp) with h15224 | h15224
                                      · linarith only [h15224, h7, hlam]
                                      · linarith only [h15224, h2, hlam]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      rcases p15193_3 (m.d 0 4) (by simp) with h15227 | h15227
                                      · linarith only [h15227, h7, hlam]
                                      · linarith only [h15227, h5, hlam]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14161, h14167, h14603, hc23, hc34, hlam, hphi, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14159, hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14159, h14161, h14603, h7, hc23, hc34, hlam, hphi, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14159, h14603, h7, hc23, hc34, hlam, hphi, p15193_1]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [h14609, hlam, p15193_0]
                                    · have p15193_0 := h15193c.1
                                      have p15193_1 := h15193c.2.1
                                      have p15193_2 := h15193c.2.2.1
                                      have p15193_3 := h15193c.2.2.2
                                      linarith only [hlam, p15193_0]
                            · linarith only [h15186, hlam, p15145_0]
                          · linarith only [h15185, h6, hlam]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h4, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h14160, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h14603, hlam, p15145_1]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h14605, hlam, p15145_1]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h5, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h14161, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h0, h14161, h14167, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p15145_1]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h14607, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h6, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h14162, hlam, p15145_0]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h0, h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p15145_1]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [h0, h14162, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p15145_1]
                        · have p15145_0 := h15145c.1
                          have p15145_1 := h15145c.2.1
                          have p15145_2 := h15145c.2.2.1
                          have p15145_3 := h15145c.2.2.2
                          linarith only [hlam, p15145_0]
                      · rcases h2bigk with h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c | h15254c
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h14167, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p15254_1]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          rcases p15254_3 (m.d 0 2) (by simp) with h15257 | h15257
                          · rcases p15254_3 (m.d 1 2) (by simp) with h15258 | h15258
                            · linarith only [h0, h15258, hlam]
                            · linarith only [h14160, h15258, hlam]
                          · linarith only [h15257, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          rcases p15254_3 (m.d 0 2) (by simp) with h15262 | h15262
                          · rcases p15254_3 (m.d 1 2) (by simp) with h15263 | h15263
                            · linarith only [h0, h15263, hlam]
                            · linarith only [h14161, h15263, hlam]
                          · linarith only [h15262, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          rcases p15254_3 (m.d 0 2) (by simp) with h15267 | h15267
                          · rcases p15254_3 (m.d 1 2) (by simp) with h15268 | h15268
                            · linarith only [h0, h15268, hlam]
                            · linarith only [h14162, h15268, hlam]
                          · linarith only [h15267, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h0, hlam, p15254_1]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          rcases p15254_3 (m.d 0 2) (by simp) with h15274 | h15274
                          · rcases p15254_3 (m.d 1 2) (by simp) with h15275 | h15275
                            · rcases p15254_3 (m.d 2 3) (by simp) with h15276 | h15276
                              · linarith only [h15276, hlam, p15254_0]
                              · rcases p15254_3 (m.d 2 4) (by simp) with h15278 | h15278
                                · linarith only [h14161, h15278, hlam]
                                · linarith only [h14603, h15278, hlam]
                            · linarith only [h15275, hlam, p15254_0]
                          · linarith only [h15274, h4, hlam]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          rcases p15254_3 (m.d 0 2) (by simp) with h15283 | h15283
                          · rcases p15254_3 (m.d 1 2) (by simp) with h15284 | h15284
                            · rcases p15254_3 (m.d 2 3) (by simp) with h15285 | h15285
                              · linarith only [h14160, h15285, hlam]
                              · rcases p15254_3 (m.d 2 4) (by simp) with h15287 | h15287
                                · linarith only [h15287, hlam, p15254_0]
                                · rcases p15254_3 (m.d 2 5) (by simp) with h15289 | h15289
                                  · linarith only [h14162, h15289, hlam]
                                  · linarith only [h14607, h15289, hlam]
                            · linarith only [h15284, hlam, p15254_0]
                          · linarith only [h15283, h5, hlam]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          rcases p15254_3 (m.d 0 2) (by simp) with h15294 | h15294
                          · rcases p15254_3 (m.d 1 2) (by simp) with h15295 | h15295
                            · rcases p15254_3 (m.d 2 3) (by simp) with h15296 | h15296
                              · linarith only [h14160, h15296, hlam]
                              · rcases p15254_3 (m.d 2 4) (by simp) with h15298 | h15298
                                · linarith only [h14161, h15298, hlam]
                                · rcases p15254_3 (m.d 2 5) (by simp) with h15300 | h15300
                                  · linarith only [h15300, hlam, p15254_0]
                                  · rcases h4bigk with h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      rcases p15302_3 (m.d 0 4) (by simp) with h15304 | h15304
                                      · rcases p15302_3 (m.d 1 4) (by simp) with h15305 | h15305
                                        · linarith only [h15305, h2, hlam]
                                        · rcases p15302_3 (m.d 2 4) (by simp) with h15307 | h15307
                                          · linarith only [h15307, h5, hlam]
                                          · rcases p15302_3 (m.d 3 4) (by simp) with h15309 | h15309
                                            · rcases p15302_3 (m.d 4 5) (by simp) with h15310 | h15310
                                              · linarith only [h14159, h15310, hlam]
                                              · linarith only [h14167, h15310, hlam]
                                            · linarith only [h14163, h15309, hlam]
                                      · linarith only [h15304, h2, hlam]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      rcases p15302_3 (m.d 0 4) (by simp) with h15315 | h15315
                                      · rcases p15302_3 (m.d 1 4) (by simp) with h15316 | h15316
                                        · linarith only [h15316, h2, hlam]
                                        · linarith only [h14161, h15316, hlam]
                                      · linarith only [h15315, h5, hlam]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h7, hlam, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14161, h14167, h14603, h7, hc23, hc34, hlam, hphi, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h2, hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14167, h14603, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14610_1, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14163, hlam, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14167, hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h5, hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14161, hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14603, hlam, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14607, hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14159, h14167, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      rcases p15302_3 (m.d 0 4) (by simp) with h15333 | h15333
                                      · linarith only [h15333, h7, hlam]
                                      · linarith only [h15333, h2, hlam]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      rcases p15302_3 (m.d 0 4) (by simp) with h15336 | h15336
                                      · linarith only [h15336, h7, hlam]
                                      · linarith only [h15336, h5, hlam]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14161, h14167, h14603, hc23, hc34, hlam, hphi, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14159, hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14159, h14161, h14603, h7, hc23, hc34, hlam, hphi, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14159, h14603, h7, hc23, hc34, hlam, hphi, p15302_1]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [h14609, hlam, p15302_0]
                                    · have p15302_0 := h15302c.1
                                      have p15302_1 := h15302c.2.1
                                      have p15302_2 := h15302c.2.2.1
                                      have p15302_3 := h15302c.2.2.2
                                      linarith only [hlam, p15302_0]
                            · linarith only [h15295, hlam, p15254_0]
                          · linarith only [h15294, h6, hlam]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h4, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h14160, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h14603, hlam, p15254_1]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h14605, hlam, p15254_1]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h5, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h14161, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h0, h14161, h14167, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p15254_1]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h14607, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h6, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h14162, hlam, p15254_0]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h0, h14162, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p14610_1, p15254_1]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [h0, h14162, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p14610_1, p15254_1]
                        · have p15254_0 := h15254c.1
                          have p15254_1 := h15254c.2.1
                          have p15254_2 := h15254c.2.2.1
                          have p15254_3 := h15254c.2.2.2
                          linarith only [hlam, p15254_0]
              · linarith only [h14162, h15026, hlam]
            · linarith only [h15025, h3, hlam]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h1, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14160, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14163, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14165, hlam, p14610_1]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h2, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14161, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14159, h14160, h14167, h7, hc23, hc34, hlam, hphi, p14610_1]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14167, hlam, p14610_1]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h3, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14162, hlam, p14610_0]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14159, h14160, h14167, h7, hc23, hc34, hlam, hphi, p14610_1]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [h14159, h14160, h14163, h14167, h7, hc23, hc34, hlam, hphi, p14610_1]
          · have p14610_0 := h14610c.1
            have p14610_1 := h14610c.2.1
            have p14610_2 := h14610c.2.2.1
            have p14610_3 := h14610c.2.2.2
            linarith only [hlam, p14610_0]
        · linarith only [h14159, h14609, h7, hlam]

set_option maxHeartbeats 5618000 in
set_option maxHeartbeats 5618000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (hg14159 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h14160 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h14161 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h14162 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h14163 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h14165 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  have h14159 := hg14159
  rcases m.htr 1 4 5 (by decide) (by decide) with h14167 | h14167
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162 h14163 h14165 h14167
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s20_x0_x0_x0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 hg14159 h14160 h14161 h14162 h14163 h14165 h14167

end R2N4
