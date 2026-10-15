import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4375 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4725 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4726 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h4727 | h4727
  · rcases m.htr 1 2 5 (by decide) (by decide) with h4728 | h4728
    · rcases m.htr 1 3 4 (by decide) (by decide) with h4729 | h4729
      · linarith only [h1, h4729, h6, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4731 | h4731
        · linarith only [h1, h4375, h4731, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4733 | h4733
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4734 | h4734
            · linarith only [h0, h4726, h4734, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4736 | h4736
              · linarith only [h1, h4375, h4726, h4736, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4738 | h4738
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4739 | h4739
                  · rcases h1bigk with h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c | h4740c
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h4727, h4738, hc01, hc45, hlam, hphi, ht0b, ht5b, p4740_1]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4743 | h4743
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4744 | h4744
                        · linarith only [h0, h4744, hlam]
                        · linarith only [h4726, h4744, hlam]
                      · linarith only [h4743, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4748 | h4748
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4749 | h4749
                        · linarith only [h0, h4749, hlam]
                        · linarith only [h4727, h4749, hlam]
                      · linarith only [h4748, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4753 | h4753
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4754 | h4754
                        · linarith only [h0, h4754, hlam]
                        · linarith only [h4728, h4754, hlam]
                      · linarith only [h4753, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h0, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4760 | h4760
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4761 | h4761
                        · rcases p4740_3 (m.d 1 3) (by simp) with h4762 | h4762
                          · linarith only [h4726, h4762, hlam]
                          · rcases p4740_3 (m.d 1 4) (by simp) with h4764 | h4764
                            · linarith only [h4727, h4764, hlam]
                            · linarith only [h4729, h4764, hlam]
                        · linarith only [h4726, h4761, hlam]
                      · linarith only [h1, h4760, hlam]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h0, h4727, h4738, hc01, hc45, hlam, hphi, ht0b, ht5b, p4740_1]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4770 | h4770
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4771 | h4771
                        · rcases p4740_3 (m.d 1 3) (by simp) with h4772 | h4772
                          · linarith only [h4726, h4772, hlam]
                          · rcases p4740_3 (m.d 1 4) (by simp) with h4774 | h4774
                            · linarith only [h4727, h4774, hlam]
                            · linarith only [h4733, h4774, hlam]
                        · linarith only [h4728, h4771, hlam]
                      · linarith only [h3, h4770, hlam]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h1, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h4726, hlam, p4740_1]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h4729, hlam, p4740_1]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h4731, hlam, p4740_1]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h2, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h4727, hlam, p4740_1]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4786 | h4786
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4787 | h4787
                        · rcases p4740_3 (m.d 1 3) (by simp) with h4788 | h4788
                          · linarith only [h4729, h4788, hlam]
                          · rcases p4740_3 (m.d 1 4) (by simp) with h4790 | h4790
                            · rcases p4740_3 (m.d 1 5) (by simp) with h4791 | h4791
                              · linarith only [h4733, h4791, hlam]
                              · linarith only [h4731, h4791, hlam]
                            · linarith only [h4729, h4790, hlam]
                        · linarith only [h4726, h4787, hlam]
                      · linarith only [h1, h4786, hlam]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4798 | h4798
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4799 | h4799
                        · rcases p4740_3 (m.d 1 3) (by simp) with h4800 | h4800
                          · linarith only [h4729, h4800, hlam]
                          · rcases p4740_3 (m.d 1 4) (by simp) with h4802 | h4802
                            · rcases p4740_3 (m.d 1 5) (by simp) with h4803 | h4803
                              · linarith only [h4733, h4803, hlam]
                              · rcases h3bigk with h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4375, h4726, hc23, hc35, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4375, hc23, hc35, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h6, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4375, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h1, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h2, h4731, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4740_1, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4729, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4731, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4726, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4734, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4736, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4726, hc23, hc34, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h1, h4375, h4726, hc23, hc34, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h1, h4726, hc23, hc35, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4726, hc23, hc35, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p4805_1]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [h4739, hlam, p4805_0]
                                · have p4805_0 := h4805c.1
                                  have p4805_1 := h4805c.2.1
                                  have p4805_2 := h4805c.2.2.1
                                  have p4805_3 := h4805c.2.2.2
                                  linarith only [hlam, p4805_0]
                            · linarith only [h4733, h4802, hlam]
                        · linarith only [h4728, h4799, hlam]
                      · linarith only [h3, h4798, hlam]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h3, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h4728, hlam, p4740_1]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      rcases p4740_3 (m.d 0 1) (by simp) with h4836 | h4836
                      · rcases p4740_3 (m.d 1 2) (by simp) with h4837 | h4837
                        · rcases p4740_3 (m.d 1 3) (by simp) with h4838 | h4838
                          · linarith only [h4731, h4838, hlam]
                          · rcases p4740_3 (m.d 1 4) (by simp) with h4840 | h4840
                            · rcases p4740_3 (m.d 1 5) (by simp) with h4841 | h4841
                              · rcases h3bigk with h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c | h4842c
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4726, h6, hc23, hc34, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h6, hc23, hc34, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h6, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4375, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h1, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h3, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4740_1, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4729, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4731, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4726, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4734, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4736, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4726, hc23, hc34, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h1, h4375, h4726, hc23, hc34, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h1, h4726, hc23, hc35, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4726, hc23, hc35, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p4842_1]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [h4739, hlam, p4842_0]
                                · have p4842_0 := h4842c.1
                                  have p4842_1 := h4842c.2.1
                                  have p4842_2 := h4842c.2.2.1
                                  have p4842_3 := h4842c.2.2.2
                                  linarith only [hlam, p4842_0]
                              · linarith only [h4731, h4841, hlam]
                            · linarith only [h4729, h4840, hlam]
                        · linarith only [h4726, h4837, hlam]
                      · linarith only [h1, h4836, hlam]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [h4733, hlam, p4740_0]
                    · have p4740_0 := h4740c.1
                      have p4740_1 := h4740c.2.1
                      have p4740_2 := h4740c.2.2.1
                      have p4740_3 := h4740c.2.2.2
                      linarith only [hlam, p4740_0]
                  · linarith only [h4738, h4739, h5, h6, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4875 | h4875
                  · rcases h1bigk with h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c | h4876c
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4727, h4733, h4734, h4738, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      rcases p4876_3 (m.d 0 1) (by simp) with h4879 | h4879
                      · rcases p4876_3 (m.d 1 2) (by simp) with h4880 | h4880
                        · linarith only [h0, h4880, hlam]
                        · linarith only [h4726, h4880, hlam]
                      · linarith only [h4879, hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4733, h4734, h4738, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      rcases p4876_3 (m.d 0 1) (by simp) with h4885 | h4885
                      · rcases p4876_3 (m.d 1 2) (by simp) with h4886 | h4886
                        · linarith only [h0, h4886, hlam]
                        · linarith only [h4728, h4886, hlam]
                      · linarith only [h4885, hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h0, hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      rcases p4876_3 (m.d 0 1) (by simp) with h4892 | h4892
                      · rcases p4876_3 (m.d 1 2) (by simp) with h4893 | h4893
                        · rcases p4876_3 (m.d 1 3) (by simp) with h4894 | h4894
                          · linarith only [h4726, h4894, hlam]
                          · rcases p4876_3 (m.d 1 4) (by simp) with h4896 | h4896
                            · linarith only [h4727, h4896, hlam]
                            · linarith only [h4729, h4896, hlam]
                        · linarith only [h4726, h4893, hlam]
                      · linarith only [h1, h4892, hlam]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h0, h4733, h4734, h4738, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h0, h4733, h4734, h4738, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h1, hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4726, hlam, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4729, hlam, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4731, hlam, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h2, hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4727, hlam, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      rcases p4876_3 (m.d 0 1) (by simp) with h4910 | h4910
                      · rcases p4876_3 (m.d 1 2) (by simp) with h4911 | h4911
                        · rcases p4876_3 (m.d 1 3) (by simp) with h4912 | h4912
                          · linarith only [h4729, h4912, hlam]
                          · rcases p4876_3 (m.d 1 4) (by simp) with h4914 | h4914
                            · rcases p4876_3 (m.d 1 5) (by simp) with h4915 | h4915
                              · linarith only [h4733, h4915, hlam]
                              · linarith only [h4731, h4915, hlam]
                            · linarith only [h4729, h4914, hlam]
                        · linarith only [h4726, h4911, hlam]
                      · linarith only [h1, h4910, hlam]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h2, h4733, h4734, h4738, h6, hc23, hc34, hlam, hphi, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h3, hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4728, hlam, p4876_1]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      rcases p4876_3 (m.d 0 1) (by simp) with h4925 | h4925
                      · rcases p4876_3 (m.d 1 2) (by simp) with h4926 | h4926
                        · rcases p4876_3 (m.d 1 3) (by simp) with h4927 | h4927
                          · linarith only [h4731, h4927, hlam]
                          · rcases p4876_3 (m.d 1 4) (by simp) with h4929 | h4929
                            · rcases p4876_3 (m.d 1 5) (by simp) with h4930 | h4930
                              · rcases h3bigk with h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c | h4931c
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h6, hc13, hc34, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h6, hc23, hc34, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h6, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4375, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h1, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4729, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4731, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4726, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4734, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4736, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4726, hc23, hc34, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h1, h4375, h4726, hc23, hc34, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h1, h4726, hc23, hc35, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4726, hc23, hc35, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p4931_1]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [h4875, hlam, p4931_0]
                                · have p4931_0 := h4931c.1
                                  have p4931_1 := h4931c.2.1
                                  have p4931_2 := h4931c.2.2.1
                                  have p4931_3 := h4931c.2.2.2
                                  linarith only [hlam, p4931_0]
                              · linarith only [h4731, h4930, hlam]
                            · linarith only [h4729, h4929, hlam]
                        · linarith only [h4726, h4926, hlam]
                      · linarith only [h1, h4925, hlam]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [h4733, hlam, p4876_0]
                    · have p4876_0 := h4876c.1
                      have p4876_1 := h4876c.2.1
                      have p4876_2 := h4876c.2.2.1
                      have p4876_3 := h4876c.2.2.2
                      linarith only [hlam, p4876_0]
                  · linarith only [h4725, h4875, h6, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4964 | h4964
            · linarith only [h4725, h4726, h4729, h4733, h4964, h6, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4966 | h4966
              · linarith only [h1, h4375, h4726, h4966, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4968 | h4968
                · linarith only [h0, h4726, h4727, h4729, h4733, h4968, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4970 | h4970
                  · rcases h1bigk with h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c | h4971c
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      rcases p4971_3 (m.d 0 1) (by simp) with h4973 | h4973
                      · rcases p4971_3 (m.d 1 2) (by simp) with h4974 | h4974
                        · linarith only [h4974, hlam, p4971_0]
                        · rcases p4971_3 (m.d 1 3) (by simp) with h4976 | h4976
                          · linarith only [h1, h4976, hlam]
                          · rcases p4971_3 (m.d 1 4) (by simp) with h4978 | h4978
                            · linarith only [h2, h4978, hlam]
                            · rcases p4971_3 (m.d 1 5) (by simp) with h4980 | h4980
                              · linarith only [h3, h4980, hlam]
                              · rcases h3bigk with h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4726, h6, hc23, hc34, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h6, hc23, hc34, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h6, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4375, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h1, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4725, h4729, h4733, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4729, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4731, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4726, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4964, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4966, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4726, hc23, hc34, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4375, h4725, h4733, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h1, h4726, hc23, hc35, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4726, hc23, hc35, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p4982_1]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [h4970, hlam, p4982_0]
                                · have p4982_0 := h4982c.1
                                  have p4982_1 := h4982c.2.1
                                  have p4982_2 := h4982c.2.2.1
                                  have p4982_3 := h4982c.2.2.2
                                  linarith only [hlam, p4982_0]
                      · linarith only [h4973, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      rcases p4971_3 (m.d 0 1) (by simp) with h5009 | h5009
                      · rcases p4971_3 (m.d 1 2) (by simp) with h5010 | h5010
                        · linarith only [h0, h5010, hlam]
                        · linarith only [h4726, h5010, hlam]
                      · linarith only [h5009, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      rcases p4971_3 (m.d 0 1) (by simp) with h5014 | h5014
                      · rcases p4971_3 (m.d 1 2) (by simp) with h5015 | h5015
                        · linarith only [h0, h5015, hlam]
                        · linarith only [h4727, h5015, hlam]
                      · linarith only [h5014, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      rcases p4971_3 (m.d 0 1) (by simp) with h5019 | h5019
                      · rcases p4971_3 (m.d 1 2) (by simp) with h5020 | h5020
                        · linarith only [h0, h5020, hlam]
                        · linarith only [h4728, h5020, hlam]
                      · linarith only [h5019, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h0, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      rcases p4971_3 (m.d 0 1) (by simp) with h5026 | h5026
                      · rcases p4971_3 (m.d 1 2) (by simp) with h5027 | h5027
                        · rcases p4971_3 (m.d 1 3) (by simp) with h5028 | h5028
                          · linarith only [h4726, h5028, hlam]
                          · rcases p4971_3 (m.d 1 4) (by simp) with h5030 | h5030
                            · linarith only [h4727, h5030, hlam]
                            · linarith only [h4729, h5030, hlam]
                        · linarith only [h4726, h5027, hlam]
                      · linarith only [h1, h5026, hlam]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      rcases p4971_3 (m.d 0 1) (by simp) with h5035 | h5035
                      · rcases p4971_3 (m.d 1 2) (by simp) with h5036 | h5036
                        · rcases p4971_3 (m.d 1 3) (by simp) with h5037 | h5037
                          · linarith only [h4726, h5037, hlam]
                          · rcases p4971_3 (m.d 1 4) (by simp) with h5039 | h5039
                            · linarith only [h4727, h5039, hlam]
                            · rcases p4971_3 (m.d 1 5) (by simp) with h5041 | h5041
                              · linarith only [h4728, h5041, hlam]
                              · linarith only [h4733, h5041, hlam]
                        · linarith only [h4727, h5036, hlam]
                      · linarith only [h2, h5035, hlam]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      rcases p4971_3 (m.d 0 1) (by simp) with h5046 | h5046
                      · rcases p4971_3 (m.d 1 2) (by simp) with h5047 | h5047
                        · rcases p4971_3 (m.d 1 3) (by simp) with h5048 | h5048
                          · linarith only [h4726, h5048, hlam]
                          · rcases p4971_3 (m.d 1 4) (by simp) with h5050 | h5050
                            · linarith only [h4727, h5050, hlam]
                            · rcases p4971_3 (m.d 1 5) (by simp) with h5052 | h5052
                              · linarith only [h4728, h5052, hlam]
                              · rcases h3bigk with h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c | h5054c
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4726, h6, hc23, hc34, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h6, hc23, hc34, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h6, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4375, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h1, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4729, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4731, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4726, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4964, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4966, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4726, hc23, hc34, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h1, h4375, h4726, hc23, hc34, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h1, h4726, hc23, hc35, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4726, hc23, hc35, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p5054_1]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [h4970, hlam, p5054_0]
                                · have p5054_0 := h5054c.1
                                  have p5054_1 := h5054c.2.1
                                  have p5054_2 := h5054c.2.2.1
                                  have p5054_3 := h5054c.2.2.2
                                  linarith only [hlam, p5054_0]
                        · linarith only [h4728, h5047, hlam]
                      · linarith only [h3, h5046, hlam]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h1, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4726, hlam, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4729, hlam, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4731, hlam, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h2, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4727, hlam, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4726, h4733, hc23, hc45, hlam, hphi, ht34, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4733, hlam, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h3, hlam, p4971_0]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4728, hlam, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4725, h4726, h4733, h6, hc23, hc34, hlam, hphi, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [h4725, h4727, h4733, h4964, h6, hc23, hc34, hlam, hphi, p4971_1]
                    · have p4971_0 := h4971c.1
                      have p4971_1 := h4971c.2.1
                      have p4971_2 := h4971c.2.2.1
                      have p4971_3 := h4971c.2.2.2
                      linarith only [hlam, p4971_0]
                  · linarith only [h4725, h4970, h6, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5098 | h5098
      · linarith only [h1, h5098, h6, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5100 | h5100
        · linarith only [h1, h4375, h5100, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5102 | h5102
          · linarith only [h4727, h4728, h5102, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5104 | h5104
            · linarith only [h4725, h4726, h5098, h5102, h5104, h6, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5106 | h5106
              · linarith only [h3, h4375, h4727, h4728, h5104, h5106, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5108 | h5108
                · linarith only [h4727, h4728, h5102, h5108, hlam]
                · linarith only [h4725, h4727, h4728, h5104, h5108, h6, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h5111 | h5111
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5112 | h5112
      · linarith only [h1, h4727, h5, h5111, h5112, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5114 | h5114
        · linarith only [h1, h4375, h5114, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5116 | h5116
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5117 | h5117
            · linarith only [h1, h4726, h5117, h6, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5119 | h5119
              · linarith only [h0, h4375, h4726, h4727, h5, h5119, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5121 | h5121
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5122 | h5122
                  · rcases h1bigk with h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c | h5123c
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      rcases p5123_3 (m.d 0 1) (by simp) with h5125 | h5125
                      · rcases p5123_3 (m.d 1 2) (by simp) with h5126 | h5126
                        · linarith only [h5126, hlam, p5123_0]
                        · rcases p5123_3 (m.d 1 3) (by simp) with h5128 | h5128
                          · linarith only [h1, h5128, hlam]
                          · rcases p5123_3 (m.d 1 4) (by simp) with h5130 | h5130
                            · linarith only [h2, h5130, hlam]
                            · linarith only [h4727, h5130, hlam]
                      · linarith only [h5125, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      rcases p5123_3 (m.d 0 1) (by simp) with h5134 | h5134
                      · rcases p5123_3 (m.d 1 2) (by simp) with h5135 | h5135
                        · linarith only [h0, h5135, hlam]
                        · linarith only [h4726, h5135, hlam]
                      · linarith only [h5134, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      rcases p5123_3 (m.d 0 1) (by simp) with h5139 | h5139
                      · rcases p5123_3 (m.d 1 2) (by simp) with h5140 | h5140
                        · linarith only [h0, h5140, hlam]
                        · rcases p5123_3 (m.d 1 3) (by simp) with h5142 | h5142
                          · linarith only [h1, h5142, hlam]
                          · rcases p5123_3 (m.d 1 4) (by simp) with h5144 | h5144
                            · linarith only [h5144, hlam, p5123_0]
                            · rcases p5123_3 (m.d 1 5) (by simp) with h5146 | h5146
                              · linarith only [h3, h5146, hlam]
                              · rcases h3bigk with h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c | h5148c
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h4375, hc13, hc35, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h4375, hc23, hc35, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h6, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h4375, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h1, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h5112, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h5114, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h4, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h4726, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h5117, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h5119, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hc13, hc34, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h4375, hc03, hc34, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hc03, hc35, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h4726, hc23, hc35, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p5148_1]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [h5122, hlam, p5148_0]
                                · have p5148_0 := h5148c.1
                                  have p5148_1 := h5148c.2.1
                                  have p5148_2 := h5148c.2.2.1
                                  have p5148_3 := h5148c.2.2.2
                                  linarith only [hlam, p5148_0]
                      · linarith only [h5139, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      rcases p5123_3 (m.d 0 1) (by simp) with h5175 | h5175
                      · rcases p5123_3 (m.d 1 2) (by simp) with h5176 | h5176
                        · linarith only [h0, h5176, hlam]
                        · linarith only [h5111, h5176, hlam]
                      · linarith only [h5175, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h0, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h0, h4726, h4727, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h4727, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h0, h4727, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h1, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h4726, hlam, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h5112, hlam, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h5114, hlam, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h2, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h2, h4726, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      rcases p5123_3 (m.d 0 1) (by simp) with h5192 | h5192
                      · rcases p5123_3 (m.d 1 2) (by simp) with h5193 | h5193
                        · linarith only [h4727, h5193, hlam]
                        · linarith only [h4726, h5193, hlam]
                      · linarith only [h1, h5192, hlam]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      rcases p5123_3 (m.d 0 1) (by simp) with h5198 | h5198
                      · rcases p5123_3 (m.d 1 2) (by simp) with h5199 | h5199
                        · linarith only [h4727, h5199, hlam]
                        · linarith only [h5111, h5199, hlam]
                      · linarith only [h3, h5198, hlam]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h3, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h5111, hlam, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h0, h4726, h4727, h5, h5111, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5123_1]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [h5116, hlam, p5123_0]
                    · have p5123_0 := h5123c.1
                      have p5123_1 := h5123c.2.1
                      have p5123_2 := h5123c.2.2.1
                      have p5123_3 := h5123c.2.2.2
                      linarith only [hlam, p5123_0]
                  · linarith only [h4725, h5122, h6, hlam]
                · linarith only [h4727, h5111, h5116, h5121, hlam]
          · linarith only [h4725, h4726, h4727, h5116, h6, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5211 | h5211
      · linarith only [h1, h4726, h4727, h5, h5211, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5213 | h5213
        · linarith only [h1, h4375, h5213, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5215 | h5215
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5216 | h5216
            · linarith only [h1, h4726, h5216, h6, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5218 | h5218
              · linarith only [h4375, h4726, h4727, h5, h5218, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5220 | h5220
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5221 | h5221
                  · rcases h1bigk with h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c | h5222c
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      rcases p5222_3 (m.d 0 1) (by simp) with h5224 | h5224
                      · rcases p5222_3 (m.d 1 2) (by simp) with h5225 | h5225
                        · linarith only [h5225, hlam, p5222_0]
                        · rcases p5222_3 (m.d 1 3) (by simp) with h5227 | h5227
                          · linarith only [h1, h5227, hlam]
                          · rcases p5222_3 (m.d 1 4) (by simp) with h5229 | h5229
                            · linarith only [h2, h5229, hlam]
                            · linarith only [h4727, h5229, hlam]
                      · linarith only [h5224, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      rcases p5222_3 (m.d 0 1) (by simp) with h5233 | h5233
                      · rcases p5222_3 (m.d 1 2) (by simp) with h5234 | h5234
                        · linarith only [h0, h5234, hlam]
                        · linarith only [h4726, h5234, hlam]
                      · linarith only [h5233, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      rcases p5222_3 (m.d 0 1) (by simp) with h5238 | h5238
                      · rcases p5222_3 (m.d 1 2) (by simp) with h5239 | h5239
                        · linarith only [h0, h5239, hlam]
                        · rcases p5222_3 (m.d 1 3) (by simp) with h5241 | h5241
                          · linarith only [h1, h5241, hlam]
                          · rcases p5222_3 (m.d 1 4) (by simp) with h5243 | h5243
                            · linarith only [h5243, hlam, p5222_0]
                            · rcases p5222_3 (m.d 1 5) (by simp) with h5245 | h5245
                              · linarith only [h3, h5245, hlam]
                              · rcases h3bigk with h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c | h5247c
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h6, hc13, hc34, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h6, hc23, hc34, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h6, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h4375, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h1, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h5211, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h5213, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h4, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h4726, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h5216, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h5218, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h4726, hc23, hc34, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h4726, h5111, h5218, hc23, hc34, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h1, h4726, hc23, hc35, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h4726, hc23, hc35, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hc23, hc35, hlam, hphi, p5247_1]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [h5221, hlam, p5247_0]
                                · have p5247_0 := h5247c.1
                                  have p5247_1 := h5247c.2.1
                                  have p5247_2 := h5247c.2.2.1
                                  have p5247_3 := h5247c.2.2.2
                                  linarith only [hlam, p5247_0]
                      · linarith only [h5238, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      rcases p5222_3 (m.d 0 1) (by simp) with h5274 | h5274
                      · rcases p5222_3 (m.d 1 2) (by simp) with h5275 | h5275
                        · linarith only [h0, h5275, hlam]
                        · rcases p5222_3 (m.d 1 3) (by simp) with h5277 | h5277
                          · linarith only [h1, h5277, hlam]
                          · rcases p5222_3 (m.d 1 4) (by simp) with h5279 | h5279
                            · linarith only [h2, h5279, hlam]
                            · linarith only [h5215, h5279, hlam]
                      · linarith only [h5274, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h0, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h0, h4726, h4727, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5222_1]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h4727, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h5111, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h1, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h4726, hlam, p5222_1]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h5211, hlam, p5222_1]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h5213, hlam, p5222_1]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h2, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h2, h4726, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5222_1]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      rcases p5222_3 (m.d 0 1) (by simp) with h5295 | h5295
                      · rcases p5222_3 (m.d 1 2) (by simp) with h5296 | h5296
                        · linarith only [h4727, h5296, hlam]
                        · linarith only [h4726, h5296, hlam]
                      · linarith only [h1, h5295, hlam]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h0, h4726, h4727, h5, h5111, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5222_1]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h3, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h3, h4726, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5222_1]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      rcases p5222_3 (m.d 0 1) (by simp) with h5304 | h5304
                      · rcases p5222_3 (m.d 1 2) (by simp) with h5305 | h5305
                        · linarith only [h5111, h5305, hlam]
                        · linarith only [h4726, h5305, hlam]
                      · linarith only [h1, h5304, hlam]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [h5215, hlam, p5222_0]
                    · have p5222_0 := h5222c.1
                      have p5222_1 := h5222c.2.1
                      have p5222_2 := h5222c.2.2.1
                      have p5222_3 := h5222c.2.2.2
                      linarith only [hlam, p5222_0]
                  · linarith only [h2, h5215, h5221, h6, hlam]
                · linarith only [h4727, h5215, h5220, hlam]
          · linarith only [h4725, h4726, h4727, h5215, h6, hc23, hc34, hlam, hphi]

end R2N4
