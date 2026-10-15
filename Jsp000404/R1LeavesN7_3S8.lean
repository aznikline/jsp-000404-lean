import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11192000 in
set_option maxHeartbeats 11192000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x1_x0 (m : N7Model)
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
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h3976 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h4749 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  rcases m.htr 1 2 5 (by decide) (by decide) with h4750 | h4750
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4751 | h4751
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4752 | h4752
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4753 | h4753
        · linarith only [h2, h4753, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4755 | h4755
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4756 | h4756
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4757 | h4757
              · linarith only [h0, h3976, h4, h4749, h4757, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4759 | h4759
                · linarith only [h2, h4749, h4755, h4759, h9, hlam]
                · rcases h1bigk with h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    rcases p4761_3 (m.d 0 1) (by simp) with h4763 | h4763
                    · rcases p4761_3 (m.d 1 2) (by simp) with h4764 | h4764
                      · linarith only [h4764, hlam, p4761_0]
                      · rcases p4761_3 (m.d 1 3) (by simp) with h4766 | h4766
                        · linarith only [h1, h4766, hlam]
                        · linarith only [h3976, h4766, hlam]
                    · linarith only [h4763, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    rcases p4761_3 (m.d 0 1) (by simp) with h4770 | h4770
                    · rcases p4761_3 (m.d 1 2) (by simp) with h4771 | h4771
                      · linarith only [h0, h4771, hlam]
                      · rcases p4761_3 (m.d 1 3) (by simp) with h4773 | h4773
                        · linarith only [h4773, hlam, p4761_0]
                        · rcases p4761_3 (m.d 1 4) (by simp) with h4775 | h4775
                          · linarith only [h2, h4775, hlam]
                          · rcases p4761_3 (m.d 1 5) (by simp) with h4777 | h4777
                            · linarith only [h3, h4777, hlam]
                            · rcases h3bigk with h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c | h4779c
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                rcases p4779_3 (m.d 0 3) (by simp) with h4781 | h4781
                                · rcases p4779_3 (m.d 1 3) (by simp) with h4782 | h4782
                                  · linarith only [h1, h4782, hlam]
                                  · rcases p4779_3 (m.d 2 3) (by simp) with h4784 | h4784
                                    · linarith only [h4, h4784, hlam]
                                    · linarith only [h3976, h4784, hlam]
                                · linarith only [h1, h4781, hlam]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h0, h3976, h4, h4749, h4755, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4779_1]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                rcases p4779_3 (m.d 0 3) (by simp) with h4789 | h4789
                                · rcases p4779_3 (m.d 1 3) (by simp) with h4790 | h4790
                                  · linarith only [h1, h4790, hlam]
                                  · linarith only [h4751, h4790, hlam]
                                · linarith only [h4789, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                rcases p4779_3 (m.d 0 3) (by simp) with h4794 | h4794
                                · rcases p4779_3 (m.d 1 3) (by simp) with h4795 | h4795
                                  · linarith only [h1, h4795, hlam]
                                  · linarith only [h4752, h4795, hlam]
                                · linarith only [h4794, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h1, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h3976, hlam, p4779_1]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4761_1, p4779_1]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p4761_1, p4779_1]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h4, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h0, h4, hlam, p4761_2, p4779_1]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                rcases p4779_3 (m.d 0 3) (by simp) with h4807 | h4807
                                · rcases p4779_3 (m.d 1 3) (by simp) with h4808 | h4808
                                  · linarith only [h3976, h4808, hlam]
                                  · linarith only [h4751, h4808, hlam]
                                · linarith only [h4807, h7, hlam]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                rcases p4779_3 (m.d 0 3) (by simp) with h4812 | h4812
                                · rcases p4779_3 (m.d 1 3) (by simp) with h4813 | h4813
                                  · linarith only [h3976, h4813, hlam]
                                  · linarith only [h4752, h4813, hlam]
                                · linarith only [h4812, h8, hlam]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h7, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h4751, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h4755, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h4759, hlam, p4779_1]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h8, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h4752, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h4756, hlam, p4779_0]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [h4752, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4761_1, p4779_1]
                              · have p4779_0 := h4779c.1
                                have p4779_1 := h4779c.2.1
                                have p4779_2 := h4779c.2.2.1
                                have p4779_3 := h4779c.2.2.2
                                linarith only [hlam, p4779_0]
                    · linarith only [h4770, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    rcases p4761_3 (m.d 0 1) (by simp) with h4828 | h4828
                    · rcases p4761_3 (m.d 1 2) (by simp) with h4829 | h4829
                      · linarith only [h0, h4829, hlam]
                      · linarith only [h4749, h4829, hlam]
                    · linarith only [h4828, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    rcases p4761_3 (m.d 0 1) (by simp) with h4833 | h4833
                    · rcases p4761_3 (m.d 1 2) (by simp) with h4834 | h4834
                      · linarith only [h0, h4834, hlam]
                      · linarith only [h4750, h4834, hlam]
                    · linarith only [h4833, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h0, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h3976, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h0, h3976, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4761_1]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h0, h3976, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p4761_1]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h1, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h0, h3976, h4, h4749, h4755, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4761_1]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    rcases p4761_3 (m.d 0 1) (by simp) with h4846 | h4846
                    · rcases p4761_3 (m.d 1 2) (by simp) with h4847 | h4847
                      · linarith only [h3976, h4847, hlam]
                      · linarith only [h4749, h4847, hlam]
                    · linarith only [h2, h4846, hlam]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    rcases p4761_3 (m.d 0 1) (by simp) with h4851 | h4851
                    · rcases p4761_3 (m.d 1 2) (by simp) with h4852 | h4852
                      · linarith only [h3976, h4852, hlam]
                      · linarith only [h4750, h4852, hlam]
                    · linarith only [h3, h4851, hlam]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h2, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h4749, hlam, p4761_1]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h4751, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h4753, hlam, p4761_1]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h3, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h4750, hlam, p4761_1]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h4752, hlam, p4761_0]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [h0, h3976, h4, h4749, h4750, h4755, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4761_1]
                  · have p4761_0 := h4761c.1
                    have p4761_1 := h4761c.2.1
                    have p4761_2 := h4761c.2.2.1
                    have p4761_3 := h4761c.2.2.2
                    linarith only [hlam, p4761_0]
            · linarith only [h0, h3976, h4, h4749, h4755, h4756, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h3976, h4755, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
      · linarith only [h3976, h4750, h4752, hlam]
    · linarith only [h3976, h4749, h4751, h7, h9, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4870 | h4870
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4871 | h4871
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4872 | h4872
        · linarith only [h2, h4872, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4874 | h4874
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4875 | h4875
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4876 | h4876
              · linarith only [h4749, h4750, h4876, h6, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4878 | h4878
                · linarith only [h4749, h4750, h4874, h4878, h6, h9, hlam]
                · rcases h1bigk with h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c | h4880c
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    rcases p4880_3 (m.d 0 1) (by simp) with h4882 | h4882
                    · rcases p4880_3 (m.d 1 2) (by simp) with h4883 | h4883
                      · linarith only [h4883, hlam, p4880_0]
                      · rcases p4880_3 (m.d 1 3) (by simp) with h4885 | h4885
                        · linarith only [h1, h4885, hlam]
                        · linarith only [h3976, h4885, hlam]
                    · linarith only [h4882, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    rcases p4880_3 (m.d 0 1) (by simp) with h4889 | h4889
                    · rcases p4880_3 (m.d 1 2) (by simp) with h4890 | h4890
                      · linarith only [h0, h4890, hlam]
                      · rcases p4880_3 (m.d 1 3) (by simp) with h4892 | h4892
                        · linarith only [h4892, hlam, p4880_0]
                        · rcases p4880_3 (m.d 1 4) (by simp) with h4894 | h4894
                          · linarith only [h2, h4894, hlam]
                          · rcases p4880_3 (m.d 1 5) (by simp) with h4896 | h4896
                            · linarith only [h3, h4896, hlam]
                            · rcases h3bigk with h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c | h4898c
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                rcases p4898_3 (m.d 0 3) (by simp) with h4900 | h4900
                                · rcases p4898_3 (m.d 1 3) (by simp) with h4901 | h4901
                                  · linarith only [h1, h4901, hlam]
                                  · rcases p4898_3 (m.d 2 3) (by simp) with h4903 | h4903
                                    · linarith only [h4, h4903, hlam]
                                    · linarith only [h3976, h4903, hlam]
                                · linarith only [h1, h4900, hlam]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h0, h3976, h4, h4749, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4898_1]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                rcases p4898_3 (m.d 0 3) (by simp) with h4908 | h4908
                                · rcases p4898_3 (m.d 1 3) (by simp) with h4909 | h4909
                                  · linarith only [h1, h4909, hlam]
                                  · linarith only [h4870, h4909, hlam]
                                · linarith only [h4908, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                rcases p4898_3 (m.d 0 3) (by simp) with h4913 | h4913
                                · rcases p4898_3 (m.d 1 3) (by simp) with h4914 | h4914
                                  · linarith only [h1, h4914, hlam]
                                  · linarith only [h4871, h4914, hlam]
                                · linarith only [h4913, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h1, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h3976, hlam, p4898_1]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4880_1, p4898_1]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p4880_1, p4898_1]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h4, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h0, h4, hlam, p4880_2, p4898_1]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                rcases p4898_3 (m.d 0 3) (by simp) with h4926 | h4926
                                · rcases p4898_3 (m.d 1 3) (by simp) with h4927 | h4927
                                  · linarith only [h3976, h4927, hlam]
                                  · linarith only [h4870, h4927, hlam]
                                · linarith only [h4926, h7, hlam]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                rcases p4898_3 (m.d 0 3) (by simp) with h4931 | h4931
                                · rcases p4898_3 (m.d 1 3) (by simp) with h4932 | h4932
                                  · linarith only [h3976, h4932, hlam]
                                  · linarith only [h4871, h4932, hlam]
                                · linarith only [h4931, h8, hlam]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h7, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h4870, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h4874, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h4878, hlam, p4898_1]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h8, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h4871, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h4875, hlam, p4898_0]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [h4871, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4880_1, p4898_1]
                              · have p4898_0 := h4898c.1
                                have p4898_1 := h4898c.2.1
                                have p4898_2 := h4898c.2.2.1
                                have p4898_3 := h4898c.2.2.2
                                linarith only [hlam, p4898_0]
                    · linarith only [h4889, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    rcases p4880_3 (m.d 0 1) (by simp) with h4947 | h4947
                    · rcases p4880_3 (m.d 1 2) (by simp) with h4948 | h4948
                      · linarith only [h0, h4948, hlam]
                      · linarith only [h4749, h4948, hlam]
                    · linarith only [h4947, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    rcases p4880_3 (m.d 0 1) (by simp) with h4952 | h4952
                    · rcases p4880_3 (m.d 1 2) (by simp) with h4953 | h4953
                      · linarith only [h0, h4953, hlam]
                      · rcases p4880_3 (m.d 1 3) (by simp) with h4955 | h4955
                        · linarith only [h1, h4955, hlam]
                        · linarith only [h4871, h4955, hlam]
                    · linarith only [h4952, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h0, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h3976, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h4750, h6, h9, hc14, hc45, hlam, hphi, p4880_1]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h4750, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h1, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h0, h3976, h4, h4749, h4874, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4880_1]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    rcases p4880_3 (m.d 0 1) (by simp) with h4967 | h4967
                    · rcases p4880_3 (m.d 1 2) (by simp) with h4968 | h4968
                      · linarith only [h3976, h4968, hlam]
                      · linarith only [h4749, h4968, hlam]
                    · linarith only [h2, h4967, hlam]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h0, h3976, h4, h4749, h4750, h4874, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4880_1]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h2, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h4749, hlam, p4880_1]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h4870, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h4872, hlam, p4880_1]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h3, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h3, h4749, h4874, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4880_1]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [h4871, hlam, p4880_0]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    rcases p4880_3 (m.d 0 1) (by simp) with h4981 | h4981
                    · rcases p4880_3 (m.d 1 2) (by simp) with h4982 | h4982
                      · linarith only [h4750, h4982, hlam]
                      · linarith only [h4749, h4982, hlam]
                    · linarith only [h2, h4981, hlam]
                  · have p4880_0 := h4880c.1
                    have p4880_1 := h4880c.2.1
                    have p4880_2 := h4880c.2.2.1
                    have p4880_3 := h4880c.2.2.2
                    linarith only [hlam, p4880_0]
            · linarith only [h3976, h4871, h4875, hlam]
          · linarith only [h3976, h4749, h4874, h7, h9, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4989 | h4989
        · linarith only [h2, h4989, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4991 | h4991
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4992 | h4992
            · linarith only [h0, h3976, h4, h4749, h4871, h4991, h4992, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h3976, h4749, h4991, h4992, h8, h9, hc34, hc45, hlam, hphi]
          · linarith only [h0, h3976, h4, h4749, h4991, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h3976, h4749, h4870, h7, h9, hc24, hc45, hlam, hphi]

end R2N4
