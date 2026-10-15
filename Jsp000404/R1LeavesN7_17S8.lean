import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S6
import Jsp000404.R1LeavesN7_17S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3761 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4051 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4276 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h4746 | h4746
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4747 | h4747
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4748 | h4748
      · linarith only [h0, h4, h4748, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4750 | h4750
        · linarith only [h0, h3761, h4750, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4752 | h4752
          · linarith only [h0, h4051, h4752, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4754 | h4754
            · linarith only [h1, h4276, h4754, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4756 | h4756
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4757 | h4757
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4758 | h4758
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4759 | h4759
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4760 | h4760
                      · rcases h0bigk with h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c
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
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4764 | h4764
                            · linarith only [h0, h4764, hlam]
                            · rcases p4761_3 (m.d 0 3) (by simp) with h4766 | h4766
                              · linarith only [h1, h4766, hlam]
                              · linarith only [h4, h4766, hlam]
                          · linarith only [h0, h4763, hlam]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4746, h4760, hc01, hc45, hlam, hphi, ht0b, ht5b, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4276, h4746, h4760, hc01, hc45, hlam, hphi, ht0b, ht5b, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          rcases p4761_3 (m.d 0 1) (by simp) with h4772 | h4772
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4773 | h4773
                            · linarith only [h0, h4773, hlam]
                            · rcases p4761_3 (m.d 0 3) (by simp) with h4775 | h4775
                              · linarith only [h1, h4775, hlam]
                              · linarith only [h4746, h4775, hlam]
                          · linarith only [h3, h4772, hlam]
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
                          linarith only [h4, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h3761, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4051, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h1, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h0, h4276, h4757, hc12, hc23, hlam, hphi, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4276, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h0, h4051, h4276, h4757, hc12, hc23, hlam, hphi, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h2, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4276, h4757, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h0, h4051, h4276, h4757, hc12, hc23, hlam, hphi, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h3, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4746, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4747, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                      · linarith only [h2, h4276, h4756, h4760, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h3, h3761, h4276, h4746, h4756, h4757, h4759, hc12, hc23, hlam, hphi]
                  · linarith only [h4276, h4746, h4757, h4758, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4802 | h4802
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4803 | h4803
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4804 | h4804
                      · rcases h0bigk with h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c | h4805c
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          rcases p4805_3 (m.d 0 1) (by simp) with h4807 | h4807
                          · rcases p4805_3 (m.d 0 2) (by simp) with h4808 | h4808
                            · linarith only [h0, h4808, hlam]
                            · rcases p4805_3 (m.d 0 3) (by simp) with h4810 | h4810
                              · linarith only [h1, h4810, hlam]
                              · linarith only [h4, h4810, hlam]
                          · linarith only [h0, h4807, hlam]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h4746, h4804, hc01, hc45, hlam, hphi, ht0b, ht5b, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h4276, h4746, h4804, hc01, hc45, hlam, hphi, ht0b, ht5b, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          rcases p4805_3 (m.d 0 1) (by simp) with h4816 | h4816
                          · rcases p4805_3 (m.d 0 2) (by simp) with h4817 | h4817
                            · linarith only [h0, h4817, hlam]
                            · rcases p4805_3 (m.d 0 3) (by simp) with h4819 | h4819
                              · linarith only [h1, h4819, hlam]
                              · linarith only [h4746, h4819, hlam]
                          · linarith only [h3, h4816, hlam]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h0, hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h4, hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h3761, hlam, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h4051, hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h1, hlam, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h0, h4, h4757, hc12, hc34, hlam, hphi, ht23, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h4276, hlam, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h0, h4, h4051, h4757, hc12, hc34, hlam, hphi, ht23, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h2, hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h0, h3761, h4757, hc12, hc34, hlam, hphi, ht23, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h3761, h4757, hc03, hc34, hlam, hphi, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h0, h3761, h4051, h4757, hc12, hc34, hlam, hphi, ht23, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h3, hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h0, h4051, h4757, h4802, hc12, hc34, hlam, hphi, ht23, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h4746, hlam, p4805_0]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [h4747, hlam, p4805_1]
                        · have p4805_0 := h4805c.1
                          have p4805_1 := h4805c.2.1
                          have p4805_2 := h4805c.2.2.1
                          have p4805_3 := h4805c.2.2.2
                          linarith only [hlam, p4805_0]
                      · linarith only [h0, h4, h4757, h4804, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h2, h3761, h4756, h4803, hlam]
                  · linarith only [h4, h4746, h4802, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4846 | h4846
                · linarith only [h4276, h4747, h4748, h4754, h4756, h4846, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4848 | h4848
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4849 | h4849
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4850 | h4850
                      · linarith only [h4, h4746, h4748, h4754, h4756, h4846, h4850, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h2, h4, h4746, h4747, h4846, h4850, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h3761, h4051, h4747, h4846, h4848, h4849, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h4, h4746, h4848, hlam]
    · linarith only [h4276, h4746, h4747, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4856 | h4856
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4857 | h4857
      · linarith only [h0, h4, h4857, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4859 | h4859
        · linarith only [h0, h3761, h4859, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4861 | h4861
          · linarith only [h0, h4051, h4861, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4863 | h4863
            · linarith only [h1, h4276, h4863, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4865 | h4865
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4866 | h4866
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4867 | h4867
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4868 | h4868
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4869 | h4869
                      · rcases h0bigk with h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c | h4870c
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          rcases p4870_3 (m.d 0 1) (by simp) with h4872 | h4872
                          · rcases p4870_3 (m.d 0 2) (by simp) with h4873 | h4873
                            · linarith only [h0, h4873, hlam]
                            · rcases p4870_3 (m.d 0 3) (by simp) with h4875 | h4875
                              · linarith only [h1, h4875, hlam]
                              · linarith only [h4, h4875, hlam]
                          · linarith only [h0, h4872, hlam]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          rcases p4870_3 (m.d 0 1) (by simp) with h4879 | h4879
                          · rcases p4870_3 (m.d 0 2) (by simp) with h4880 | h4880
                            · linarith only [h0, h4880, hlam]
                            · rcases p4870_3 (m.d 0 3) (by simp) with h4882 | h4882
                              · linarith only [h1, h4882, hlam]
                              · rcases p4870_3 (m.d 0 4) (by simp) with h4884 | h4884
                                · linarith only [h2, h4884, hlam]
                                · linarith only [h4276, h4884, hlam]
                          · linarith only [h1, h4879, hlam]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h2, h4865, hc01, hc45, hlam, hphi, ht0b, ht5b, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          rcases p4870_3 (m.d 0 1) (by simp) with h4889 | h4889
                          · rcases p4870_3 (m.d 0 2) (by simp) with h4890 | h4890
                            · linarith only [h0, h4890, hlam]
                            · rcases p4870_3 (m.d 0 3) (by simp) with h4892 | h4892
                              · linarith only [h1, h4892, hlam]
                              · rcases p4870_3 (m.d 0 4) (by simp) with h4894 | h4894
                                · linarith only [h2, h4894, hlam]
                                · linarith only [h4856, h4894, hlam]
                          · linarith only [h3, h4889, hlam]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h0, hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h4, hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h3761, hlam, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h4051, hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h1, hlam, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h0, h4746, h4866, h4869, hc12, hc23, hlam, hphi, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h4276, hlam, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h4746, hlam, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h2, hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h4276, h4866, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h0, h4, h4276, h4746, h4866, hc12, hc23, hlam, hphi, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h3, hlam, p4870_0]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h0, h4, h4746, h4866, h4869, hc12, hc23, hlam, hphi, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [h4856, hlam, p4870_1]
                        · have p4870_0 := h4870c.1
                          have p4870_1 := h4870c.2.1
                          have p4870_2 := h4870c.2.2.1
                          have p4870_3 := h4870c.2.2.2
                          linarith only [hlam, p4870_0]
                      · linarith only [h2, h4276, h4865, h4869, hlam]
                    · linarith only [h0, h2, h3761, h4865, h4868, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h4, h4276, h4866, h4867, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4921 | h4921
                  · linarith only [h0, h4, h4746, h4866, h4921, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4923 | h4923
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4924 | h4924
                      · rcases h0bigk with h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c | h4925c
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          rcases p4925_3 (m.d 0 1) (by simp) with h4927 | h4927
                          · rcases p4925_3 (m.d 0 2) (by simp) with h4928 | h4928
                            · linarith only [h0, h4928, hlam]
                            · rcases p4925_3 (m.d 0 3) (by simp) with h4930 | h4930
                              · linarith only [h1, h4930, hlam]
                              · linarith only [h4, h4930, hlam]
                          · linarith only [h0, h4927, hlam]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          rcases p4925_3 (m.d 0 1) (by simp) with h4934 | h4934
                          · rcases p4925_3 (m.d 0 2) (by simp) with h4935 | h4935
                            · linarith only [h0, h4935, hlam]
                            · rcases p4925_3 (m.d 0 3) (by simp) with h4937 | h4937
                              · linarith only [h1, h4937, hlam]
                              · rcases p4925_3 (m.d 0 4) (by simp) with h4939 | h4939
                                · linarith only [h2, h4939, hlam]
                                · linarith only [h4276, h4939, hlam]
                          · linarith only [h1, h4934, hlam]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h2, h4865, hc01, hc45, hlam, hphi, ht0b, ht5b, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          rcases p4925_3 (m.d 0 1) (by simp) with h4944 | h4944
                          · rcases p4925_3 (m.d 0 2) (by simp) with h4945 | h4945
                            · linarith only [h0, h4945, hlam]
                            · rcases p4925_3 (m.d 0 3) (by simp) with h4947 | h4947
                              · linarith only [h1, h4947, hlam]
                              · rcases p4925_3 (m.d 0 4) (by simp) with h4949 | h4949
                                · linarith only [h2, h4949, hlam]
                                · linarith only [h4856, h4949, hlam]
                          · linarith only [h3, h4944, hlam]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h0, hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h4, hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h3761, hlam, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h4051, hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h1, hlam, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h0, h4, h4921, h4924, hc12, hc34, hlam, hphi, ht23, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h4276, hlam, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h4746, hlam, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h2, hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h4276, hc03, hc34, hlam, hphi, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h1, h4276, h4746, h4857, hc12, hc34, hlam, hphi, ht23, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h3, hlam, p4925_0]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h1, h4746, h4857, h4924, hc12, hc34, hlam, hphi, ht23, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [h4856, hlam, p4925_1]
                        · have p4925_0 := h4925c.1
                          have p4925_1 := h4925c.2.1
                          have p4925_2 := h4925c.2.2.1
                          have p4925_3 := h4925c.2.2.2
                          linarith only [hlam, p4925_0]
                      · linarith only [h2, h3761, h4865, h4866, h4924, hlam]
                    · linarith only [h2, h3761, h4865, h4923, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4975 | h4975
                · linarith only [h4276, h4856, h4857, h4863, h4865, h4975, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4977 | h4977
                  · linarith only [h1, h4746, h4857, h4975, h4977, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4979 | h4979
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4980 | h4980
                      · rcases h0bigk with h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c | h4981c
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          rcases p4981_3 (m.d 0 1) (by simp) with h4983 | h4983
                          · rcases p4981_3 (m.d 0 2) (by simp) with h4984 | h4984
                            · linarith only [h0, h4984, hlam]
                            · rcases p4981_3 (m.d 0 3) (by simp) with h4986 | h4986
                              · linarith only [h1, h4986, hlam]
                              · linarith only [h4, h4986, hlam]
                          · linarith only [h0, h4983, hlam]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          rcases p4981_3 (m.d 0 1) (by simp) with h4990 | h4990
                          · rcases p4981_3 (m.d 0 2) (by simp) with h4991 | h4991
                            · linarith only [h0, h4991, hlam]
                            · rcases p4981_3 (m.d 0 3) (by simp) with h4993 | h4993
                              · linarith only [h1, h4993, hlam]
                              · rcases p4981_3 (m.d 0 4) (by simp) with h4995 | h4995
                                · linarith only [h2, h4995, hlam]
                                · linarith only [h4276, h4995, hlam]
                          · linarith only [h1, h4990, hlam]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4856, h4857, h4863, h4865, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4856, h4857, h4863, h4865, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h0, hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4, hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h3761, hlam, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4051, hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h1, hlam, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h0, h4, h4977, h4980, hc12, hc34, hlam, hphi, ht23, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4276, hlam, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4746, hlam, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h2, hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4276, hc03, hc34, hlam, hphi, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h3, h4276, h4857, h4863, h4865, hc12, hc34, hlam, hphi, ht23, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h3, hlam, p4981_0]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h1, h4746, h4857, h4980, hc12, hc34, hlam, hphi, ht23, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [h4856, hlam, p4981_1]
                        · have p4981_0 := h4981c.1
                          have p4981_1 := h4981c.2.1
                          have p4981_2 := h4981c.2.2.1
                          have p4981_3 := h4981c.2.2.2
                          linarith only [hlam, p4981_0]
                      · linarith only [h3761, h4856, h4975, h4980, hlam]
                    · linarith only [h3761, h4856, h4979, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5023 | h5023
      · linarith only [h0, h4, h5023, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5025 | h5025
        · linarith only [h0, h3761, h5025, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5027 | h5027
          · linarith only [h2, h4051, h4856, h5025, h5027, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5029 | h5029
            · linarith only [h1, h4276, h5029, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5031 | h5031
              · linarith only [h2, h4856, h5031, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5033 | h5033
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5034 | h5034
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5035 | h5035
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5036 | h5036
                      · linarith only [h0, h3761, h4856, h5033, h5036, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h4, h4276, h5035, h5036, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5039 | h5039
                      · linarith only [h0, h3761, h5035, h5039, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c | h5041c
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          rcases p5041_3 (m.d 0 1) (by simp) with h5043 | h5043
                          · rcases p5041_3 (m.d 0 2) (by simp) with h5044 | h5044
                            · linarith only [h0, h5044, hlam]
                            · rcases p5041_3 (m.d 0 3) (by simp) with h5046 | h5046
                              · linarith only [h1, h5046, hlam]
                              · linarith only [h4, h5046, hlam]
                          · linarith only [h0, h5043, hlam]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          rcases p5041_3 (m.d 0 1) (by simp) with h5050 | h5050
                          · rcases p5041_3 (m.d 0 2) (by simp) with h5051 | h5051
                            · linarith only [h0, h5051, hlam]
                            · rcases p5041_3 (m.d 0 3) (by simp) with h5053 | h5053
                              · linarith only [h1, h5053, hlam]
                              · rcases p5041_3 (m.d 0 4) (by simp) with h5055 | h5055
                                · linarith only [h2, h5055, hlam]
                                · linarith only [h4276, h5055, hlam]
                          · linarith only [h1, h5050, hlam]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          rcases p5041_3 (m.d 0 1) (by simp) with h5059 | h5059
                          · rcases p5041_3 (m.d 0 2) (by simp) with h5060 | h5060
                            · linarith only [h0, h5060, hlam]
                            · rcases p5041_3 (m.d 0 3) (by simp) with h5062 | h5062
                              · linarith only [h1, h5062, hlam]
                              · rcases p5041_3 (m.d 0 4) (by simp) with h5064 | h5064
                                · linarith only [h2, h5064, hlam]
                                · rcases p5041_3 (m.d 0 5) (by simp) with h5066 | h5066
                                  · linarith only [h3, h5066, hlam]
                                  · linarith only [h4856, h5066, hlam]
                          · linarith only [h2, h5059, hlam]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          rcases p5041_3 (m.d 0 1) (by simp) with h5070 | h5070
                          · rcases p5041_3 (m.d 0 2) (by simp) with h5071 | h5071
                            · linarith only [h0, h5071, hlam]
                            · rcases p5041_3 (m.d 0 3) (by simp) with h5073 | h5073
                              · linarith only [h1, h5073, hlam]
                              · rcases p5041_3 (m.d 0 4) (by simp) with h5075 | h5075
                                · linarith only [h2, h5075, hlam]
                                · rcases p5041_3 (m.d 0 5) (by simp) with h5077 | h5077
                                  · linarith only [h3, h5077, hlam]
                                  · rcases h0emin with h5079 | h5079 | h5079 | h5079 | h5079
                                    · rcases h2bigk with h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c | h5080c
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h4, h4276, h5033, hc12, hc24, hlam, hphi, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h4, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h3761, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h4051, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h0, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h5023, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h5025, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h5027, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        rcases p5080_3 (m.d 0 2) (by simp) with h5091 | h5091
                                        · linarith only [h5091, hlam, p5080_0]
                                        · rcases p5080_3 (m.d 1 2) (by simp) with h5093 | h5093
                                          · linarith only [h5023, h5093, hlam]
                                          · rcases p5080_3 (m.d 2 3) (by simp) with h5095 | h5095
                                            · rcases p5080_3 (m.d 2 4) (by simp) with h5096 | h5096
                                              · linarith only [h5033, h5096, hlam]
                                              · linarith only [h3761, h5096, hlam]
                                            · linarith only [h5095, hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        rcases p5080_3 (m.d 0 2) (by simp) with h5100 | h5100
                                        · linarith only [h4, h5100, hlam]
                                        · linarith only [h0, h5100, hlam]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h3761, hc02, hc23, hlam, hphi, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h0, h4051, hc12, hc23, hlam, hphi, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h0, h5035, hc12, hc45, hlam, hphi, ht23, ht34, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h5035, hc12, hc45, hlam, hphi, ht23, ht34, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h5033, hlam, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [hlam, p5080_0]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h5035, hlam, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        rcases p5080_3 (m.d 0 2) (by simp) with h5111 | h5111
                                        · linarith only [h5111, hlam, p5080_0]
                                        · rcases p5080_3 (m.d 1 2) (by simp) with h5113 | h5113
                                          · linarith only [h5027, h5113, hlam]
                                          · rcases p5080_3 (m.d 2 3) (by simp) with h5115 | h5115
                                            · rcases p5080_3 (m.d 2 4) (by simp) with h5116 | h5116
                                              · linarith only [h5035, h5116, hlam]
                                              · linarith only [h3761, h5116, hlam]
                                            · linarith only [h4, h5115, hlam]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        rcases p5080_3 (m.d 0 2) (by simp) with h5120 | h5120
                                        · linarith only [h4051, h5120, hlam]
                                        · linarith only [h0, h5120, hlam]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h5034, hlam, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [h0, h3761, hc12, hc25, hlam, hphi, p5080_1]
                                      · have p5080_0 := h5080c.1
                                        have p5080_1 := h5080c.2.1
                                        have p5080_2 := h5080c.2.2.1
                                        have p5080_3 := h5080c.2.2.2
                                        linarith only [hlam, p5080_0]
                                    · linarith only [h4, h5079, hc23, hlam, ht01, ht12]
                                    · linarith only [h4276, h5079, hc34, hlam, ht01, ht12, ht23]
                                    · linarith only [h4856, h5079, hc01, hlam, p5041_1]
                                    · linarith only [h5079, hc01, hlam, p5041_1]
                          · linarith only [h3, h5070, hlam]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h0, hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4, hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h3761, hlam, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4051, hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h1, hlam, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4276, h5039, hc02, hc35, hlam, hphi, ht23, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4276, hlam, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4746, hlam, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h2, hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h0, h3761, hc12, hc24, hlam, hphi, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4276, h5039, hc03, hc35, hlam, hphi, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4856, hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h3, hlam, p5041_0]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h1, h4746, h5023, hc12, hc35, hlam, hphi, ht23, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [h4856, hc04, hc45, hlam, hphi, p5041_1]
                        · have p5041_0 := h5041c.1
                          have p5041_1 := h5041c.2.1
                          have p5041_2 := h5041c.2.2.1
                          have p5041_3 := h5041c.2.2.2
                          linarith only [hlam, p5041_0]
                  · linarith only [h1, h4276, h5023, h5033, h5034, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5152 | h5152
                  · linarith only [h1, h4746, h5023, h5033, h5152, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5154 | h5154
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5155 | h5155
                      · rcases h0bigk with h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c | h5156c
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          rcases p5156_3 (m.d 0 1) (by simp) with h5158 | h5158
                          · rcases p5156_3 (m.d 0 2) (by simp) with h5159 | h5159
                            · linarith only [h0, h5159, hlam]
                            · rcases p5156_3 (m.d 0 3) (by simp) with h5161 | h5161
                              · linarith only [h1, h5161, hlam]
                              · linarith only [h4, h5161, hlam]
                          · linarith only [h0, h5158, hlam]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          rcases p5156_3 (m.d 0 1) (by simp) with h5165 | h5165
                          · rcases p5156_3 (m.d 0 2) (by simp) with h5166 | h5166
                            · linarith only [h0, h5166, hlam]
                            · rcases p5156_3 (m.d 0 3) (by simp) with h5168 | h5168
                              · linarith only [h1, h5168, hlam]
                              · rcases p5156_3 (m.d 0 4) (by simp) with h5170 | h5170
                                · linarith only [h2, h5170, hlam]
                                · linarith only [h4276, h5170, hlam]
                          · linarith only [h1, h5165, hlam]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          rcases p5156_3 (m.d 0 1) (by simp) with h5174 | h5174
                          · rcases p5156_3 (m.d 0 2) (by simp) with h5175 | h5175
                            · linarith only [h0, h5175, hlam]
                            · rcases p5156_3 (m.d 0 3) (by simp) with h5177 | h5177
                              · linarith only [h1, h5177, hlam]
                              · rcases p5156_3 (m.d 0 4) (by simp) with h5179 | h5179
                                · linarith only [h2, h5179, hlam]
                                · rcases p5156_3 (m.d 0 5) (by simp) with h5181 | h5181
                                  · linarith only [h3, h5181, hlam]
                                  · linarith only [h4856, h5181, hlam]
                          · linarith only [h2, h5174, hlam]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          rcases p5156_3 (m.d 0 1) (by simp) with h5185 | h5185
                          · rcases p5156_3 (m.d 0 2) (by simp) with h5186 | h5186
                            · linarith only [h0, h5186, hlam]
                            · rcases p5156_3 (m.d 0 3) (by simp) with h5188 | h5188
                              · linarith only [h1, h5188, hlam]
                              · rcases p5156_3 (m.d 0 4) (by simp) with h5190 | h5190
                                · linarith only [h2, h5190, hlam]
                                · rcases p5156_3 (m.d 0 5) (by simp) with h5192 | h5192
                                  · linarith only [h3, h5192, hlam]
                                  · rcases h0emin with h5194 | h5194 | h5194 | h5194 | h5194
                                    · rcases h2bigk with h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c | h5195c
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h4, h5152, h5155, hc12, hc34, hlam, hphi, ht23, p5195_1]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h4, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h3761, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h4051, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h0, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5023, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5025, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5027, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5152, h5155, hc02, hc34, hlam, hphi, ht23, p5195_1]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5152, h5155, hc12, hc34, hlam, hphi, ht23, p5195_1]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5033, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5152, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        rcases p5195_3 (m.d 0 2) (by simp) with h5211 | h5211
                                        · linarith only [h5211, hlam, p5195_0]
                                        · rcases p5195_3 (m.d 1 2) (by simp) with h5213 | h5213
                                          · linarith only [h5025, h5213, hlam]
                                          · rcases p5195_3 (m.d 2 3) (by simp) with h5215 | h5215
                                            · linarith only [h5033, h5215, hlam]
                                            · linarith only [h4, h5215, hlam]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        rcases p5195_3 (m.d 0 2) (by simp) with h5218 | h5218
                                        · linarith only [h3761, h5218, hlam]
                                        · linarith only [h0, h5218, hlam]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h0, h4, h5033, hc12, hc34, hlam, hphi, ht23, p5195_1]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h0, h4051, h5033, hc12, hc34, hlam, hphi, ht23, p5195_1]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        rcases p5195_3 (m.d 0 2) (by simp) with h5224 | h5224
                                        · linarith only [h5224, hlam, p5195_0]
                                        · rcases p5195_3 (m.d 1 2) (by simp) with h5226 | h5226
                                          · linarith only [h5027, h5226, hlam]
                                          · rcases p5195_3 (m.d 2 3) (by simp) with h5228 | h5228
                                            · linarith only [h5152, h5228, hlam]
                                            · linarith only [h4, h5228, hlam]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        rcases p5195_3 (m.d 0 2) (by simp) with h5231 | h5231
                                        · linarith only [h4051, h5231, hlam]
                                        · linarith only [h0, h5231, hlam]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p5195_1]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [h5154, hlam, p5195_0]
                                      · have p5195_0 := h5195c.1
                                        have p5195_1 := h5195c.2.1
                                        have p5195_2 := h5195c.2.2.1
                                        have p5195_3 := h5195c.2.2.2
                                        linarith only [hlam, p5195_0]
                                    · linarith only [h4, h5194, hc23, hlam, ht01, ht12]
                                    · linarith only [h0, h4051, h4276, h5194, hc01, hc12, hc34, hlam, hphi, ht23, p5156_1]
                                    · linarith only [h1, h4746, h4856, h5023, h5033, h5154, h5194, hc01, hc12, hc34, hlam, hphi, ht23, p5156_1]
                                    · linarith only [h5194, hc01, hlam, p5156_1]
                          · linarith only [h3, h5185, hlam]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h0, hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h4, hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h3761, hlam, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h4051, hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h1, hlam, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h4276, hlam, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h4746, hlam, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h2, hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h0, h3761, h5033, hc12, hc34, hlam, hphi, ht23, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h3761, h5033, hc03, hc34, hlam, hphi, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h4856, hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h3, hlam, p5156_0]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h0, h4051, hc12, hc25, hlam, hphi, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h1, h4746, h5023, h5155, hc12, hc34, hlam, hphi, ht23, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [h4856, h5033, h5154, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5156_1]
                        · have p5156_0 := h5156c.1
                          have p5156_1 := h5156c.2.1
                          have p5156_2 := h5156c.2.2.1
                          have p5156_3 := h5156c.2.2.2
                          linarith only [hlam, p5156_0]
                      · linarith only [h5033, h5154, h5155, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5263 | h5263
                      · linarith only [h0, h4, h5033, h5154, h5263, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h4, h5033, h5263, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3761 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4051 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h4276 | h4276
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h3761 h4051 h4276
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h3761 h4051 h4276

set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3761 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h4051 | h4051
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h3761 h4051
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h3761 h4051

set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h3761 | h3761
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h3761
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x1_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h3761

set_option maxHeartbeats 10524000 in
set_option maxHeartbeats 10524000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 10818000 in
set_option maxHeartbeats 10818000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_14_H_I_L_I_L_I_s3 m hb0 hb2 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h5266 | h5266
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5267 | h5267
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5268 | h5268
        · linarith only [h0, h3, h5268, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5270 | h5270
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5271 | h5271
            · linarith only [h1, h3, h5271, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5273 | h5273
              · linarith only [h2, h3, h5273, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5275 | h5275
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5276 | h5276
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5277 | h5277
                    · linarith only [h0, h3, h5268, h5277, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5279 | h5279
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5280 | h5280
                        · linarith only [h2, h3, h5273, h5280, hlam]
                        · linarith only [h0, h3, h5275, h5280, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h5270, h5271, h5279, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h3, h5267, h5275, h5276, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h5266, h5268, h5275, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5286 | h5286
            · linarith only [h1, h3, h5286, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5288 | h5288
              · linarith only [h0, h3, h5267, h5288, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5290 | h5290
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5291 | h5291
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5292 | h5292
                    · linarith only [h0, h5268, h5292, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5294 | h5294
                      · linarith only [h1, h5270, h5294, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5296 | h5296
                        · linarith only [h2, h3, h5288, h5296, hlam]
                        · linarith only [h0, h3, h5290, h5296, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h3, h5267, h5290, h5291, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h5266, h5268, h5290, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5301 | h5301
        · linarith only [h2, h3, h5267, h5301, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5303 | h5303
          · linarith only [h5266, h5267, h5303, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5305 | h5305
            · linarith only [h2, h3, h5266, h5267, h5305, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5307 | h5307
              · linarith only [h2, h3, h5307, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5309 | h5309
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5310 | h5310
                  · linarith only [h0, h5267, h5310, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5312 | h5312
                    · linarith only [h0, h5301, h5312, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5314 | h5314
                      · linarith only [h1, h3, h5303, h5312, h5314, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5316 | h5316
                        · linarith only [h0, h2, h3, h5303, h5307, h5309, h5316, hc23, hc34, hlam, hphi]
                        · linarith only [h2, h3, h5309, h5310, h5316, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h5266, h5267, h5307, h5309, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5320 | h5320
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5321 | h5321
        · linarith only [h1, h3, h5266, h5321, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5323 | h5323
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5324 | h5324
            · linarith only [h1, h3, h5324, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5326 | h5326
              · linarith only [h1, h3, h5266, h5320, h5326, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5328 | h5328
                · linarith only [h0, h3, h5266, h5320, h5328, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5330 | h5330
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5331 | h5331
                    · linarith only [h0, h3, h5321, h5331, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5333 | h5333
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5334 | h5334
                        · linarith only [h2, h3, h5326, h5334, hlam]
                        · linarith only [h1, h3, h5333, h5334, hc34, hc45, hlam, hphi]
                      · linarith only [h1, h3, h5323, h5328, h5330, h5331, h5333, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h5266, h5320, h5324, h5330, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h5266, h5320, h5323, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5340 | h5340
        · linarith only [h0, h3, h5340, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5342 | h5342
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5343 | h5343
            · linarith only [h1, h3, h5343, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5345 | h5345
              · linarith only [h1, h3, h5342, h5345, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5347 | h5347
                · linarith only [h0, h5266, h5347, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5349 | h5349
                  · linarith only [h1, h3, h5320, h5347, h5349, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5351 | h5351
                    · linarith only [h0, h3, h5340, h5351, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5353 | h5353
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5354 | h5354
                        · linarith only [h1, h3, h5345, h5353, h5354, hlam]
                        · linarith only [h1, h3, h5353, h5354, hc34, hc45, hlam, hphi]
                      · linarith only [h5342, h5343, h5353, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5358 | h5358
            · linarith only [h2, h3, h5342, h5358, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5360 | h5360
              · linarith only [h2, h3, h5360, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5362 | h5362
                · linarith only [h0, h3, h5266, h5362, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5364 | h5364
                  · linarith only [h1, h5320, h5342, h5362, h5364, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5366 | h5366
                    · linarith only [h0, h5340, h5366, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5368 | h5368
                      · linarith only [h1, h5342, h5368, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5370 | h5370
                        · linarith only [h2, h5360, h5370, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5372 | h5372
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5373 | h5373
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5374 | h5374
                              · linarith only [h0, h3, h5370, h5374, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5376 | h5376
                                · linarith only [h0, h5320, h5374, h5376, hc12, hc34, hlam, hphi, ht23]
                                · rcases h0bigk with h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c | h5378c
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h0, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h0, h3, h5266, h5358, h5373, hc12, hc23, hlam, hphi, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h3, h5358, h5373, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h3, hlam, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h0, hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5266, hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5320, hlam, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5340, hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h1, hlam, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h0, h5342, h5372, hc12, hc24, hlam, hphi, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5342, hlam, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5358, hlam, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h2, hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h0, h2, h3, h5366, h5374, hc12, hc45, hlam, hphi, ht23, ht34, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h2, h3, h5366, h5374, hc03, hc45, hlam, hphi, ht34, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5360, hlam, p5378_0]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5358, h5373, hc01, hc23, hlam, hphi, ht12, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h0, h5358, h5373, hc12, hc23, hlam, hphi, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h1, h5358, h5362, h5373, hc12, hc23, hlam, hphi, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [h5358, h5373, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5378_1]
                                  · have p5378_0 := h5378c.1
                                    have p5378_1 := h5378c.2.1
                                    have p5378_2 := h5378c.2.2.1
                                    have p5378_3 := h5378c.2.2.2
                                    linarith only [hlam, p5378_0]
                            · linarith only [h1, h5342, h5362, h5372, h5373, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5405 | h5405
                            · linarith only [h1, h5358, h5362, h5372, h5405, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5407 | h5407
                              · linarith only [h2, h3, h5362, h5368, h5370, h5407, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5409 | h5409
                                · linarith only [h0, h5266, h5372, h5407, h5409, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h5266, h5372, h5409, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
