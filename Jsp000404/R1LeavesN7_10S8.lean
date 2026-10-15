import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4281 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4724 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h4725 | h4725
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4726 | h4726
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4727 | h4727
      · linarith only [h0, h2, h4727, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4729 | h4729
        · linarith only [h0, h4281, h4729, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4731 | h4731
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4732 | h4732
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4733 | h4733
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4734 | h4734
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4735 | h4735
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4736 | h4736
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4737 | h4737
                      · rcases h2bigk with h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c | h4738c
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4281, h4734, hc12, hc23, hlam, hphi, p4738_1]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h2, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4281, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4743 | h4743
                          · rcases p4738_3 (m.d 1 2) (by simp) with h4744 | h4744
                            · linarith only [h0, h4744, hlam]
                            · linarith only [h4731, h4744, hlam]
                          · linarith only [h4743, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h0, hlam, p4738_1]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4727, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4729, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4752 | h4752
                          · rcases p4738_3 (m.d 1 2) (by simp) with h4753 | h4753
                            · rcases p4738_3 (m.d 2 3) (by simp) with h4754 | h4754
                              · rcases p4738_3 (m.d 2 4) (by simp) with h4755 | h4755
                                · rcases p4738_3 (m.d 2 5) (by simp) with h4756 | h4756
                                  · linarith only [h4756, hlam, p4738_0]
                                  · rcases h4bigk with h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c | h4758c
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4725, h4729, h4735, h4737, hc03, hc45, hlam, hphi, ht0b, ht5b, p4738_1, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4281, hlam, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h2, h4725, h4737, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      rcases p4758_3 (m.d 0 4) (by simp) with h4763 | h4763
                                      · rcases p4758_3 (m.d 1 4) (by simp) with h4764 | h4764
                                        · linarith only [h1, h4764, hlam]
                                        · linarith only [h4733, h4764, hlam]
                                      · linarith only [h4763, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h1, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4729, hlam, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4737, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4281, h4734, hc02, hc23, hlam, hphi, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4729, h4734, h4735, h4737, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4738_1, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4734, h4737, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      rcases p4758_3 (m.d 0 4) (by simp) with h4777 | h4777
                                      · linarith only [h4281, h4777, hlam]
                                      · linarith only [h4726, h4777, hlam]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4725, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4732, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4734, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h2, h4725, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4758_1]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4726, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4733, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4736, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [h4737, hlam, p4758_0]
                                    · have p4758_0 := h4758c.1
                                      have p4758_1 := h4758c.2.1
                                      have p4758_2 := h4758c.2.2.1
                                      have p4758_3 := h4758c.2.2.2
                                      linarith only [hlam, p4758_0]
                                · linarith only [h4736, h4755, hlam]
                              · linarith only [h4735, h4754, hlam]
                            · linarith only [h4753, hlam, p4738_0]
                          · linarith only [h4724, h4752, hlam]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4794 | h4794
                          · linarith only [h4794, hlam, p4738_0]
                          · rcases p4738_3 (m.d 1 2) (by simp) with h4796 | h4796
                            · linarith only [h4727, h4796, hlam]
                            · rcases p4738_3 (m.d 2 3) (by simp) with h4798 | h4798
                              · rcases p4738_3 (m.d 2 4) (by simp) with h4799 | h4799
                                · linarith only [h4734, h4799, hlam]
                                · linarith only [h4281, h4799, hlam]
                              · linarith only [h4798, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4803 | h4803
                          · linarith only [h2, h4803, hlam]
                          · linarith only [h0, h4803, hlam]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4281, hc02, hc23, hlam, hphi, p4738_1]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4808 | h4808
                          · linarith only [h2, h4808, hlam]
                          · linarith only [h4724, h4808, hlam]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4811 | h4811
                          · linarith only [h4811, hlam, p4738_0]
                          · rcases p4738_3 (m.d 1 2) (by simp) with h4813 | h4813
                            · linarith only [h4729, h4813, hlam]
                            · rcases p4738_3 (m.d 2 3) (by simp) with h4815 | h4815
                              · rcases p4738_3 (m.d 2 4) (by simp) with h4816 | h4816
                                · rcases p4738_3 (m.d 2 5) (by simp) with h4817 | h4817
                                  · linarith only [h4736, h4817, hlam]
                                  · rcases h4bigk with h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4729, h4731, h4735, h4737, hc04, hc45, hlam, hphi, ht0b, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4281, hlam, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4737, hc04, hc45, hlam, hphi, ht0b, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      rcases p4819_3 (m.d 0 4) (by simp) with h4824 | h4824
                                      · rcases p4819_3 (m.d 1 4) (by simp) with h4825 | h4825
                                        · linarith only [h1, h4825, hlam]
                                        · linarith only [h4733, h4825, hlam]
                                      · linarith only [h4824, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h1, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4729, hlam, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4737, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h0, h4281, h4731, h4734, h4735, h4737, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4729, h4731, h4734, h4735, h4737, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4734, h4737, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      rcases p4819_3 (m.d 0 4) (by simp) with h4838 | h4838
                                      · linarith only [h4281, h4838, hlam]
                                      · linarith only [h4726, h4838, hlam]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4725, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4732, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4734, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h2, h4725, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4819_1]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4726, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4733, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4736, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [h4737, hlam, p4819_0]
                                    · have p4819_0 := h4819c.1
                                      have p4819_1 := h4819c.2.1
                                      have p4819_2 := h4819c.2.2.1
                                      have p4819_3 := h4819c.2.2.2
                                      linarith only [hlam, p4819_0]
                                · linarith only [h4816, hlam, p4738_0]
                              · linarith only [h2, h4815, hlam]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4853 | h4853
                          · linarith only [h4281, h4853, hlam]
                          · linarith only [h0, h4853, hlam]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4734, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          rcases p4738_3 (m.d 0 2) (by simp) with h4858 | h4858
                          · linarith only [h4281, h4858, hlam]
                          · linarith only [h4724, h4858, hlam]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4724, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4731, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4735, hlam, p4738_0]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [h4736, hlam, p4738_1]
                        · have p4738_0 := h4738c.1
                          have p4738_1 := h4738c.2.1
                          have p4738_2 := h4738c.2.2.1
                          have p4738_3 := h4738c.2.2.2
                          linarith only [hlam, p4738_0]
                      · rcases h2bigk with h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c | h4866c
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h2, hc12, hc23, hlam, hphi, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h2, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4281, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4281, h4734, h4736, h4737, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h0, hlam, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4727, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4729, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h0, h4736, h4737, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4724, h4736, h4737, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4731, h4736, h4737, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h1, h4281, h4733, h4737, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          rcases p4866_3 (m.d 0 2) (by simp) with h4881 | h4881
                          · linarith only [h2, h4881, hlam]
                          · linarith only [h4724, h4881, hlam]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h0, h4731, h4736, h4737, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4731, h4736, h4737, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4734, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          rcases p4866_3 (m.d 0 2) (by simp) with h4888 | h4888
                          · linarith only [h4281, h4888, hlam]
                          · linarith only [h4724, h4888, hlam]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4724, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4731, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4735, hlam, p4866_0]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [h4736, hlam, p4866_1]
                        · have p4866_0 := h4866c.1
                          have p4866_1 := h4866c.2.1
                          have p4866_2 := h4866c.2.2.1
                          have p4866_3 := h4866c.2.2.2
                          linarith only [hlam, p4866_0]
                    · linarith only [h0, h1, h4281, h4726, h4731, h4736, hc01, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h4281, h4731, h4734, h4735, hlam]
                · linarith only [h2, h4725, h4734, hlam]
              · linarith only [h4729, h4731, h4733, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4900 | h4900
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4901 | h4901
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4902 | h4902
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4903 | h4903
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4904 | h4904
                      · rcases h2bigk with h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c | h4905c
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h2, h4731, h4902, h4904, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h2, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4281, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4910 | h4910
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4911 | h4911
                            · linarith only [h0, h4911, hlam]
                            · linarith only [h4731, h4911, hlam]
                          · linarith only [h4910, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h0, hlam, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4727, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4729, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h2, h4725, h4727, h4732, h4902, h4904, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4920 | h4920
                          · linarith only [h4920, hlam, p4905_0]
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4922 | h4922
                            · linarith only [h4727, h4922, hlam]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4924 | h4924
                              · rcases p4905_3 (m.d 2 4) (by simp) with h4925 | h4925
                                · linarith only [h4901, h4925, hlam]
                                · linarith only [h4281, h4925, hlam]
                              · linarith only [h4924, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4929 | h4929
                          · linarith only [h2, h4929, hlam]
                          · linarith only [h0, h4929, hlam]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4281, hc02, hc23, hlam, hphi, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h2, h4725, h4727, h4731, h4732, hlam, p4905_2]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4935 | h4935
                          · linarith only [h4935, hlam, p4905_0]
                          · rcases p4905_3 (m.d 1 2) (by simp) with h4937 | h4937
                            · linarith only [h4729, h4937, hlam]
                            · rcases p4905_3 (m.d 2 3) (by simp) with h4939 | h4939
                              · rcases p4905_3 (m.d 2 4) (by simp) with h4940 | h4940
                                · rcases p4905_3 (m.d 2 5) (by simp) with h4941 | h4941
                                  · linarith only [h4903, h4941, hlam]
                                  · rcases h4bigk with h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c | h4943c
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4729, h4731, h4902, h4904, hc04, hc45, hlam, hphi, ht0b, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4281, hlam, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4725, h4727, h4731, h4732, h4902, h4904, hc03, hc45, hlam, hphi, ht0b, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      rcases p4943_3 (m.d 0 4) (by simp) with h4948 | h4948
                                      · rcases p4943_3 (m.d 1 4) (by simp) with h4949 | h4949
                                        · linarith only [h1, h4949, hlam]
                                        · linarith only [h4900, h4949, hlam]
                                      · linarith only [h4948, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h1, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4729, hlam, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4732, hlam, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h0, h4281, h4731, h4901, h4902, h4904, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4729, h4731, h4901, h4902, h4904, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4727, h4731, h4732, h4901, h4902, h4904, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      rcases p4943_3 (m.d 0 4) (by simp) with h4962 | h4962
                                      · linarith only [h4281, h4962, hlam]
                                      · linarith only [h4726, h4962, hlam]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4725, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4725, h4727, h4731, h4732, h4902, h4904, hc04, hc45, hlam, hphi, ht0b, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4901, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h2, h4725, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4943_1]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4726, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4900, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4903, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [h4904, hlam, p4943_0]
                                    · have p4943_0 := h4943c.1
                                      have p4943_1 := h4943c.2.1
                                      have p4943_2 := h4943c.2.2.1
                                      have p4943_3 := h4943c.2.2.2
                                      linarith only [hlam, p4943_0]
                                · linarith only [h4940, hlam, p4905_0]
                              · linarith only [h2, h4939, hlam]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4977 | h4977
                          · linarith only [h4281, h4977, hlam]
                          · linarith only [h0, h4977, hlam]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4901, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          rcases p4905_3 (m.d 0 2) (by simp) with h4982 | h4982
                          · linarith only [h4281, h4982, hlam]
                          · linarith only [h4724, h4982, hlam]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4724, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4731, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4902, hlam, p4905_0]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [h4903, hlam, p4905_1]
                        · have p4905_0 := h4905c.1
                          have p4905_1 := h4905c.2.1
                          have p4905_2 := h4905c.2.2.1
                          have p4905_3 := h4905c.2.2.2
                          linarith only [hlam, p4905_0]
                      · linarith only [h2, h4725, h4726, h4727, h4731, h4732, h4902, h4904, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h4281, h4731, h4900, h4902, h4903, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h2, h4725, h4727, h4732, h4902, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h2, h4725, h4901, hlam]
              · linarith only [h4727, h4731, h4732, h4900, hlam]
          · linarith only [h2, h4724, h4731, hc12, hc23, hlam, hphi]
    · linarith only [h4281, h4724, h4726, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4997 | h4997
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4998 | h4998
      · linarith only [h0, h2, h4724, h4998, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5000 | h5000
        · linarith only [h0, h2, h4281, h4725, h5000, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5002 | h5002
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5003 | h5003
            · linarith only [h1, h4725, h5003, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5005 | h5005
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5006 | h5006
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5007 | h5007
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5008 | h5008
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5009 | h5009
                      · rcases h2bigk with h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c | h5010c
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h2, h5002, h5007, h5009, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5010_1]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h2, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h4281, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h2, h4725, h5006, h5007, h5009, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5010_1]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h0, hlam, p5010_1]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h4998, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h5000, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h0, h2, h4725, h5006, h5007, h5009, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5010_1]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          rcases p5010_3 (m.d 0 2) (by simp) with h5021 | h5021
                          · linarith only [h5021, hlam, p5010_0]
                          · rcases p5010_3 (m.d 1 2) (by simp) with h5023 | h5023
                            · linarith only [h4998, h5023, hlam]
                            · rcases p5010_3 (m.d 2 3) (by simp) with h5025 | h5025
                              · rcases p5010_3 (m.d 2 4) (by simp) with h5026 | h5026
                                · linarith only [h5006, h5026, hlam]
                                · linarith only [h4281, h5026, hlam]
                              · linarith only [h5025, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          rcases p5010_3 (m.d 0 2) (by simp) with h5030 | h5030
                          · linarith only [h2, h5030, hlam]
                          · linarith only [h0, h5030, hlam]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h2, h4725, h5006, hc02, hc23, hlam, hphi, p5010_1]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h0, h2, h4725, h5002, h5006, hlam, p5010_2]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          rcases p5010_3 (m.d 0 2) (by simp) with h5036 | h5036
                          · linarith only [h5036, hlam, p5010_0]
                          · rcases p5010_3 (m.d 1 2) (by simp) with h5038 | h5038
                            · linarith only [h5000, h5038, hlam]
                            · rcases p5010_3 (m.d 2 3) (by simp) with h5040 | h5040
                              · rcases p5010_3 (m.d 2 4) (by simp) with h5041 | h5041
                                · rcases p5010_3 (m.d 2 5) (by simp) with h5042 | h5042
                                  · linarith only [h5008, h5042, hlam]
                                  · rcases h4bigk with h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c | h5044c
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h4725, h5006, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h4281, hlam, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h4725, hlam, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h4725, h5006, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h1, hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5000, hlam, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5003, hlam, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h0, h4281, h5002, h5007, h5009, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5000, h5002, h5007, h5009, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h0, h2, h4725, h5002, h5006, h5007, h5009, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      rcases p5044_3 (m.d 0 4) (by simp) with h5059 | h5059
                                      · linarith only [h4281, h5059, hlam]
                                      · linarith only [h4997, h5059, hlam]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h0, h2, h4725, h5002, h5007, h5009, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h4998, h5002, h5003, h5007, h5009, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5006, hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5006, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5044_1]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h4997, hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5005, hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5008, hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [h5009, hlam, p5044_0]
                                    · have p5044_0 := h5044c.1
                                      have p5044_1 := h5044c.2.1
                                      have p5044_2 := h5044c.2.2.1
                                      have p5044_3 := h5044c.2.2.2
                                      linarith only [hlam, p5044_0]
                                · linarith only [h5041, hlam, p5010_0]
                              · linarith only [h2, h5040, hlam]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          rcases p5010_3 (m.d 0 2) (by simp) with h5074 | h5074
                          · linarith only [h4281, h5074, hlam]
                          · linarith only [h0, h5074, hlam]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h5006, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          rcases p5010_3 (m.d 0 2) (by simp) with h5079 | h5079
                          · linarith only [h4281, h5079, hlam]
                          · linarith only [h4724, h5079, hlam]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h4724, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h5002, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h5007, hlam, p5010_0]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [h5008, hlam, p5010_1]
                        · have p5010_0 := h5010c.1
                          have p5010_1 := h5010c.2.1
                          have p5010_2 := h5010c.2.2.1
                          have p5010_3 := h5010c.2.2.2
                          linarith only [hlam, p5010_0]
                      · linarith only [h0, h2, h4725, h4997, h5002, h5009, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h4281, h5002, h5005, h5007, h5008, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h2, h4725, h5006, h5007, hc02, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5090 | h5090
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5091 | h5091
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5092 | h5092
                      · rcases h2bigk with h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c | h5093c
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h2, h5002, h5090, h5092, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h2, hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h4281, hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h2, h5006, h5090, h5092, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h0, hlam, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h4998, hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h5000, hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h0, h2, h5006, h5090, h5092, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h5006, hc02, hc34, hlam, hphi, ht23, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h5006, hc12, hc34, hlam, hphi, ht23, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h5006, hlam, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          rcases p5093_3 (m.d 0 2) (by simp) with h5108 | h5108
                          · linarith only [h2, h5108, hlam]
                          · linarith only [h4724, h5108, hlam]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          rcases p5093_3 (m.d 0 2) (by simp) with h5111 | h5111
                          · linarith only [h5111, hlam, p5093_0]
                          · rcases p5093_3 (m.d 1 2) (by simp) with h5113 | h5113
                            · linarith only [h5000, h5113, hlam]
                            · rcases p5093_3 (m.d 2 3) (by simp) with h5115 | h5115
                              · linarith only [h5006, h5115, hlam]
                              · linarith only [h2, h5115, hlam]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          rcases p5093_3 (m.d 0 2) (by simp) with h5118 | h5118
                          · linarith only [h4281, h5118, hlam]
                          · linarith only [h0, h5118, hlam]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h2, h5006, hc02, hc34, hlam, hphi, ht23, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          rcases p5093_3 (m.d 0 2) (by simp) with h5123 | h5123
                          · linarith only [h4281, h5123, hlam]
                          · linarith only [h4724, h5123, hlam]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h4724, hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h5002, hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h5090, hlam, p5093_0]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [h5091, hlam, p5093_1]
                        · have p5093_0 := h5093c.1
                          have p5093_1 := h5093c.2.1
                          have p5093_2 := h5093c.2.2.1
                          have p5093_3 := h5093c.2.2.2
                          linarith only [hlam, p5093_0]
                      · linarith only [h4725, h4997, h5092, hlam]
                    · linarith only [h0, h4281, h5002, h5005, h5091, hlam]
                  · linarith only [h0, h2, h5002, h5090, hlam]
              · linarith only [h4998, h5002, h5003, h5005, hlam]
          · linarith only [h2, h4724, h5002, hc12, hc23, hlam, hphi]
    · linarith only [h2, h4724, h4725, h4997, hlam]

end R2N4
