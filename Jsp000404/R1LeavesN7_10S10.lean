import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S6
import Jsp000404.R1LeavesN7_10S7
import Jsp000404.R1LeavesN7_10S8
import Jsp000404.R1LeavesN7_10S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x1_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4281 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4724 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h5137 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h5790 | h5790
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5791 | h5791
    · linarith only [h0, h2, h5791, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5793 | h5793
      · linarith only [h0, h4281, h5793, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5795 | h5795
        · linarith only [h0, h4724, h5795, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5797 | h5797
          · linarith only [h1, h5137, h5797, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5799 | h5799
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5800 | h5800
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5801 | h5801
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5802 | h5802
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5803 | h5803
                    · rcases h2bigk with h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c | h5804c
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h2, h5137, h5800, hc12, hc24, hlam, hphi, p5804_1]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h2, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h4281, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h4724, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h0, hlam, p5804_1]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h5791, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h5793, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h5795, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        rcases p5804_3 (m.d 0 2) (by simp) with h5815 | h5815
                        · linarith only [h5815, hlam, p5804_0]
                        · rcases p5804_3 (m.d 1 2) (by simp) with h5817 | h5817
                          · linarith only [h5791, h5817, hlam]
                          · rcases p5804_3 (m.d 2 3) (by simp) with h5819 | h5819
                            · rcases p5804_3 (m.d 2 4) (by simp) with h5820 | h5820
                              · linarith only [h5800, h5820, hlam]
                              · linarith only [h4281, h5820, hlam]
                            · linarith only [h5819, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        rcases p5804_3 (m.d 0 2) (by simp) with h5824 | h5824
                        · linarith only [h2, h5824, hlam]
                        · linarith only [h0, h5824, hlam]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h4281, hc02, hc23, hlam, hphi, p5804_1]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h0, h4724, hc12, hc23, hlam, hphi, p5804_1]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        rcases p5804_3 (m.d 0 2) (by simp) with h5830 | h5830
                        · linarith only [h5830, hlam, p5804_0]
                        · rcases p5804_3 (m.d 1 2) (by simp) with h5832 | h5832
                          · linarith only [h5793, h5832, hlam]
                          · rcases p5804_3 (m.d 2 3) (by simp) with h5834 | h5834
                            · rcases p5804_3 (m.d 2 4) (by simp) with h5835 | h5835
                              · rcases p5804_3 (m.d 2 5) (by simp) with h5836 | h5836
                                · linarith only [h5802, h5836, hlam]
                                · linarith only [h4724, h5836, hlam]
                              · linarith only [h5835, hlam, p5804_0]
                            · linarith only [h2, h5834, hlam]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        rcases p5804_3 (m.d 0 2) (by simp) with h5841 | h5841
                        · linarith only [h4281, h5841, hlam]
                        · linarith only [h0, h5841, hlam]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h5800, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h0, h4724, hc12, hc24, hlam, hphi, p5804_1]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        rcases p5804_3 (m.d 0 2) (by simp) with h5847 | h5847
                        · linarith only [h5847, hlam, p5804_0]
                        · rcases p5804_3 (m.d 1 2) (by simp) with h5849 | h5849
                          · linarith only [h5795, h5849, hlam]
                          · rcases p5804_3 (m.d 2 3) (by simp) with h5851 | h5851
                            · rcases p5804_3 (m.d 2 4) (by simp) with h5852 | h5852
                              · rcases p5804_3 (m.d 2 5) (by simp) with h5853 | h5853
                                · rcases h4bigk with h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c | h5854c
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5137, h5800, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h4281, hlam, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5137, hlam, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5137, h5800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h1, hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5793, hlam, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5797, hlam, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h0, h4281, h5800, hc12, hc23, hlam, hphi, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5793, h5800, hc12, hc23, hlam, hphi, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5137, h5800, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    rcases p5854_3 (m.d 0 4) (by simp) with h5869 | h5869
                                    · linarith only [h4281, h5869, hlam]
                                    · linarith only [h5790, h5869, hlam]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h1, h5799, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5799, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5800, hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5800, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5854_1]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5790, hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5799, hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5802, hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [h5803, hlam, p5854_0]
                                  · have p5854_0 := h5854c.1
                                    have p5854_1 := h5854c.2.1
                                    have p5854_2 := h5854c.2.2.1
                                    have p5854_3 := h5854c.2.2.2
                                    linarith only [hlam, p5854_0]
                                · linarith only [h5853, hlam, p5804_0]
                              · linarith only [h4281, h5852, hlam]
                            · linarith only [h2, h5851, hlam]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        rcases p5804_3 (m.d 0 2) (by simp) with h5885 | h5885
                        · linarith only [h4724, h5885, hlam]
                        · linarith only [h0, h5885, hlam]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h5801, hlam, p5804_0]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [h5802, hlam, p5804_1]
                      · have p5804_0 := h5804c.1
                        have p5804_1 := h5804c.2.1
                        have p5804_2 := h5804c.2.2.1
                        have p5804_3 := h5804c.2.2.2
                        linarith only [hlam, p5804_0]
                    · linarith only [h0, h1, h2, h5137, h5799, h5803, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h4281, h5137, h5799, h5800, h5802, hc12, hc23, hlam, hphi]
                · linarith only [h5797, h5800, h5801, hc13, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5894 | h5894
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5895 | h5895
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5896 | h5896
                    · rcases h2bigk with h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c | h5897c
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h4724, h5894, hc12, hc23, hlam, hphi, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h2, hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h4281, hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h4724, hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h0, hlam, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5791, hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5793, hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5795, hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5800, hc02, hc34, hlam, hphi, ht23, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5800, hc12, hc34, hlam, hphi, ht23, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5800, hlam, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h0, h4724, h5800, hc12, hc34, hlam, hphi, ht23, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        rcases p5897_3 (m.d 0 2) (by simp) with h5913 | h5913
                        · linarith only [h5913, hlam, p5897_0]
                        · rcases p5897_3 (m.d 1 2) (by simp) with h5915 | h5915
                          · linarith only [h5793, h5915, hlam]
                          · rcases p5897_3 (m.d 2 3) (by simp) with h5917 | h5917
                            · linarith only [h5800, h5917, hlam]
                            · linarith only [h2, h5917, hlam]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        rcases p5897_3 (m.d 0 2) (by simp) with h5920 | h5920
                        · linarith only [h4281, h5920, hlam]
                        · linarith only [h0, h5920, hlam]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h0, h2, h5800, hc12, hc34, hlam, hphi, ht23, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h0, h4724, h5800, hc12, hc34, hlam, hphi, ht23, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h0, h5800, h5894, hc12, hc34, hlam, hphi, ht23, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5800, h5894, hc12, hc34, hlam, hphi, ht23, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5894, hlam, p5897_0]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [h5895, hlam, p5897_1]
                      · have p5897_0 := h5897c.1
                        have p5897_1 := h5897c.2.1
                        have p5897_2 := h5897c.2.2.1
                        have p5897_3 := h5897c.2.2.2
                        linarith only [hlam, p5897_0]
                    · linarith only [h1, h5799, h5800, h5896, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4281, h5790, h5895, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5933 | h5933
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5934 | h5934
                    · rcases h2bigk with h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c | h5935c
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h2, hc12, hc23, hlam, hphi, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h2, hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h4281, hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h4724, hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h0, hlam, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5791, hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5793, hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5795, hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5894, h5934, hc02, hc34, hlam, hphi, ht23, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5894, h5934, hc12, hc34, hlam, hphi, ht23, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5800, hlam, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5894, hlam, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        rcases p5935_3 (m.d 0 2) (by simp) with h5951 | h5951
                        · linarith only [h5951, hlam, p5935_0]
                        · rcases p5935_3 (m.d 1 2) (by simp) with h5953 | h5953
                          · linarith only [h5793, h5953, hlam]
                          · rcases p5935_3 (m.d 2 3) (by simp) with h5955 | h5955
                            · linarith only [h5800, h5955, hlam]
                            · linarith only [h2, h5955, hlam]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        rcases p5935_3 (m.d 0 2) (by simp) with h5958 | h5958
                        · linarith only [h4281, h5958, hlam]
                        · linarith only [h0, h5958, hlam]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h0, h2, h5800, hc12, hc34, hlam, hphi, ht23, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [hlam, p5935_0]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h0, h4724, h5800, hc12, hc34, hlam, hphi, ht23, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        rcases p5935_3 (m.d 0 2) (by simp) with h5964 | h5964
                        · linarith only [h5964, hlam, p5935_0]
                        · rcases p5935_3 (m.d 1 2) (by simp) with h5966 | h5966
                          · linarith only [h5795, h5966, hlam]
                          · rcases p5935_3 (m.d 2 3) (by simp) with h5968 | h5968
                            · linarith only [h5894, h5968, hlam]
                            · linarith only [h2, h5968, hlam]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        rcases p5935_3 (m.d 0 2) (by simp) with h5971 | h5971
                        · linarith only [h4724, h5971, hlam]
                        · linarith only [h0, h5971, hlam]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h0, h2, hc12, hc25, hlam, hphi, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [h5933, hlam, p5935_1]
                      · have p5935_0 := h5935c.1
                        have p5935_1 := h5935c.2.1
                        have p5935_2 := h5935c.2.2.1
                        have p5935_3 := h5935c.2.2.2
                        linarith only [hlam, p5935_0]
                    · linarith only [h1, h4281, h5799, h5800, h5934, hlam]
                  · linarith only [h1, h4281, h5799, h5933, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5979 | h5979
              · linarith only [h5137, h5790, h5791, h5797, h5799, h5979, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5981 | h5981
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5982 | h5982
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5983 | h5983
                    · linarith only [h5791, h5797, h5799, h5979, h5981, h5983, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h5790, h5979, h5981, h5983, hc04, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4281, h5790, h5982, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5987 | h5987
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5988 | h5988
                    · rcases h2bigk with h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c | h5989c
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h2, h5981, h5988, hc12, hc34, hlam, hphi, ht23, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h2, hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h4281, hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h4724, hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h0, hlam, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5791, hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5793, hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5795, hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5981, h5988, hc02, hc34, hlam, hphi, ht23, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5981, h5988, hc12, hc34, hlam, hphi, ht23, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5979, hlam, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5981, hlam, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        rcases p5989_3 (m.d 0 2) (by simp) with h6005 | h6005
                        · linarith only [h6005, hlam, p5989_0]
                        · rcases p5989_3 (m.d 1 2) (by simp) with h6007 | h6007
                          · linarith only [h5793, h6007, hlam]
                          · rcases p5989_3 (m.d 2 3) (by simp) with h6009 | h6009
                            · linarith only [h5979, h6009, hlam]
                            · linarith only [h2, h6009, hlam]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        rcases p5989_3 (m.d 0 2) (by simp) with h6012 | h6012
                        · linarith only [h4281, h6012, hlam]
                        · linarith only [h0, h6012, hlam]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h0, h2, hc12, hc24, hlam, hphi, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [hlam, p5989_0]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h4724, h5790, h5791, h5797, h5799, h5979, hc12, hc34, hlam, hphi, ht23, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        rcases p5989_3 (m.d 0 2) (by simp) with h6018 | h6018
                        · linarith only [h6018, hlam, p5989_0]
                        · rcases p5989_3 (m.d 1 2) (by simp) with h6020 | h6020
                          · linarith only [h5795, h6020, hlam]
                          · rcases p5989_3 (m.d 2 3) (by simp) with h6022 | h6022
                            · linarith only [h5981, h6022, hlam]
                            · linarith only [h2, h6022, hlam]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        rcases p5989_3 (m.d 0 2) (by simp) with h6025 | h6025
                        · linarith only [h4724, h6025, hlam]
                        · linarith only [h0, h6025, hlam]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h0, h2, hc12, hc25, hlam, hphi, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [h5987, hlam, p5989_1]
                      · have p5989_0 := h5989c.1
                        have p5989_1 := h5989c.2.1
                        have p5989_2 := h5989c.2.2.1
                        have p5989_3 := h5989c.2.2.2
                        linarith only [hlam, p5989_0]
                    · linarith only [h4281, h5790, h5979, h5988, hlam]
                  · linarith only [h4281, h5790, h5987, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h6033 | h6033
    · linarith only [h0, h2, h6033, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h6035 | h6035
      · linarith only [h0, h4281, h6035, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h6037 | h6037
        · linarith only [h0, h4724, h6037, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6039 | h6039
          · linarith only [h1, h5137, h6039, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6041 | h6041
            · linarith only [h1, h5790, h6041, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6043 | h6043
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6044 | h6044
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6045 | h6045
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6046 | h6046
                    · linarith only [h0, h4281, h5790, h6043, h6046, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h2, h5137, h6043, h6045, h6046, hc12, hc23, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6049 | h6049
                    · linarith only [h0, h4281, h6045, h6049, hc12, hc34, hlam, hphi, ht23]
                    · rcases h2bigk with h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c | h6051c
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h2, h5137, h6043, hc12, hc24, hlam, hphi, p6051_1]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h2, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h4281, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h4724, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h0, hlam, p6051_1]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h6033, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h6035, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h6037, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        rcases p6051_3 (m.d 0 2) (by simp) with h6062 | h6062
                        · linarith only [h6062, hlam, p6051_0]
                        · rcases p6051_3 (m.d 1 2) (by simp) with h6064 | h6064
                          · linarith only [h6033, h6064, hlam]
                          · rcases p6051_3 (m.d 2 3) (by simp) with h6066 | h6066
                            · rcases p6051_3 (m.d 2 4) (by simp) with h6067 | h6067
                              · linarith only [h6043, h6067, hlam]
                              · linarith only [h4281, h6067, hlam]
                            · linarith only [h6066, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        rcases p6051_3 (m.d 0 2) (by simp) with h6071 | h6071
                        · linarith only [h2, h6071, hlam]
                        · linarith only [h0, h6071, hlam]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h2, h5137, h6043, hc02, hc23, hlam, hphi, p6051_1]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h0, h4724, hc12, hc23, hlam, hphi, p6051_1]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h0, h6045, hc12, hc45, hlam, hphi, ht23, ht34, p6051_1]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h6045, hc12, hc45, hlam, hphi, ht23, ht34, p6051_1]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h6043, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h6045, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        rcases p6051_3 (m.d 0 2) (by simp) with h6082 | h6082
                        · linarith only [h6082, hlam, p6051_0]
                        · rcases p6051_3 (m.d 1 2) (by simp) with h6084 | h6084
                          · linarith only [h6037, h6084, hlam]
                          · rcases p6051_3 (m.d 2 3) (by simp) with h6086 | h6086
                            · rcases p6051_3 (m.d 2 4) (by simp) with h6087 | h6087
                              · linarith only [h6045, h6087, hlam]
                              · linarith only [h4281, h6087, hlam]
                            · linarith only [h2, h6086, hlam]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        rcases p6051_3 (m.d 0 2) (by simp) with h6091 | h6091
                        · linarith only [h4724, h6091, hlam]
                        · linarith only [h0, h6091, hlam]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h6044, hlam, p6051_0]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [h0, h4281, hc12, hc25, hlam, hphi, p6051_1]
                      · have p6051_0 := h6051c.1
                        have p6051_1 := h6051c.2.1
                        have p6051_2 := h6051c.2.2.1
                        have p6051_3 := h6051c.2.2.2
                        linarith only [hlam, p6051_0]
                · linarith only [h0, h2, h5137, h6043, h6044, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6098 | h6098
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6099 | h6099
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6100 | h6100
                    · linarith only [h0, h2, h5137, h5790, h6043, h6098, h6100, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h6043, h6098, h6099, h6100, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h6043, h6098, h6099, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6104 | h6104
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6105 | h6105
                    · rcases h2bigk with h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c | h6106c
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h2, h5137, h5790, h6104, hc12, hc24, hlam, hphi, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h2, hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h4281, hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h4724, hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h0, hlam, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6033, hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6035, hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6037, hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6098, hc02, hc35, hlam, hphi, ht23, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6098, hc12, hc35, hlam, hphi, ht23, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6043, hlam, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6098, hlam, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        rcases p6106_3 (m.d 0 2) (by simp) with h6122 | h6122
                        · linarith only [h6122, hlam, p6106_0]
                        · rcases p6106_3 (m.d 1 2) (by simp) with h6124 | h6124
                          · linarith only [h6035, h6124, hlam]
                          · rcases p6106_3 (m.d 2 3) (by simp) with h6126 | h6126
                            · linarith only [h6043, h6126, hlam]
                            · linarith only [h2, h6126, hlam]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        rcases p6106_3 (m.d 0 2) (by simp) with h6129 | h6129
                        · linarith only [h4281, h6129, hlam]
                        · linarith only [h0, h6129, hlam]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h0, h2, h6043, hc12, hc34, hlam, hphi, ht23, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [hlam, p6106_0]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h0, h4724, h6043, hc12, hc34, hlam, hphi, ht23, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        rcases p6106_3 (m.d 0 2) (by simp) with h6135 | h6135
                        · linarith only [h6135, hlam, p6106_0]
                        · rcases p6106_3 (m.d 1 2) (by simp) with h6137 | h6137
                          · linarith only [h6037, h6137, hlam]
                          · rcases p6106_3 (m.d 2 3) (by simp) with h6139 | h6139
                            · linarith only [h6098, h6139, hlam]
                            · linarith only [h2, h6139, hlam]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        rcases p6106_3 (m.d 0 2) (by simp) with h6142 | h6142
                        · linarith only [h4724, h6142, hlam]
                        · linarith only [h0, h6142, hlam]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h0, h2, hc12, hc25, hlam, hphi, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [h6104, hlam, p6106_1]
                      · have p6106_0 := h6106c.1
                        have p6106_1 := h6106c.2.1
                        have p6106_2 := h6106c.2.2.1
                        have p6106_3 := h6106c.2.2.2
                        linarith only [hlam, p6106_0]
                    · linarith only [h6043, h6104, h6105, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6149 | h6149
                    · linarith only [h0, h2, h6043, h6104, h6149, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h2, h6043, h6149, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4281 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4724 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h5137 | h5137
  · exact r1l7_12_24_L_I_H_I_s1_x1_x1_x1_x0 m hb2 hb4 hg0 hg1 h2 h4281 h4724 h5137
  · exact r1l7_12_24_L_I_H_I_s1_x1_x1_x1_x1 m hb2 hb4 hg0 hg1 h2 h4281 h4724 h5137

set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4281 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h4724 | h4724
  · exact r1l7_12_24_L_I_H_I_s1_x1_x1_x0 m hb2 hb4 hg0 hg1 h2 h4281 h4724
  · exact r1l7_12_24_L_I_H_I_s1_x1_x1_x1 m hb2 hb4 hg0 hg1 h2 h4281 h4724

set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h2 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h4281 | h4281
  · exact r1l7_12_24_L_I_H_I_s1_x1_x0 m hb2 hb4 hg0 hg1 h2 h4281
  · exact r1l7_12_24_L_I_H_I_s1_x1_x1 m hb2 hb4 hg0 hg1 h2 h4281

set_option maxHeartbeats 12300000 in
set_option maxHeartbeats 12300000 in
theorem r1l7_12_24_L_I_H_I_s1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
  · exact r1l7_12_24_L_I_H_I_s1_x0 m hb2 hb4 hg0 hg1 h2
  · exact r1l7_12_24_L_I_H_I_s1_x1 m hb2 hb4 hg0 hg1 h2

end R2N4
