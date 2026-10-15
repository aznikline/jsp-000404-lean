import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S18
import Jsp000404.R1LeavesN7_3S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12604 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 0 4 5 (by decide) (by decide) with h12834 | h12834
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12835 | h12835
    · linarith only [h0, h12835, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12837 | h12837
      · linarith only [h0, h12837, h8674, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12839 | h12839
        · linarith only [h0, h12604, h12839, h4, h9870, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12841 | h12841
          · linarith only [h1, h10361, h12841, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12843 | h12843
            · linarith only [h1, h12604, h12843, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12845 | h12845
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12846 | h12846
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12847 | h12847
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12848 | h12848
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12849 | h12849
                      · rcases h1bigk with h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c | h12850c
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          rcases p12850_3 (m.d 0 1) (by simp) with h12852 | h12852
                          · rcases p12850_3 (m.d 1 2) (by simp) with h12853 | h12853
                            · linarith only [h12853, hlam, p12850_0]
                            · rcases p12850_3 (m.d 1 3) (by simp) with h12855 | h12855
                              · linarith only [h1, h12855, hlam]
                              · linarith only [h12835, h12855, hlam]
                          · linarith only [h12852, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          rcases p12850_3 (m.d 0 1) (by simp) with h12859 | h12859
                          · rcases p12850_3 (m.d 1 2) (by simp) with h12860 | h12860
                            · linarith only [h0, h12860, hlam]
                            · rcases p12850_3 (m.d 1 3) (by simp) with h12862 | h12862
                              · linarith only [h12862, hlam, p12850_0]
                              · rcases p12850_3 (m.d 1 4) (by simp) with h12864 | h12864
                                · linarith only [h12864, h2, hlam]
                                · linarith only [h12841, h12864, hlam]
                          · linarith only [h12859, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          rcases p12850_3 (m.d 0 1) (by simp) with h12868 | h12868
                          · rcases p12850_3 (m.d 1 2) (by simp) with h12869 | h12869
                            · linarith only [h0, h12869, hlam]
                            · rcases p12850_3 (m.d 1 3) (by simp) with h12871 | h12871
                              · linarith only [h1, h12871, hlam]
                              · rcases p12850_3 (m.d 1 4) (by simp) with h12873 | h12873
                                · linarith only [h12873, hlam, p12850_0]
                                · rcases p12850_3 (m.d 1 5) (by simp) with h12875 | h12875
                                  · linarith only [h12875, h3, hlam]
                                  · rcases h3bigk with h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c | h12877c
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12604, h12846, h12849, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h4, hlam, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h10361, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12604, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h1, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12835, hlam, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12841, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12843, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      rcases p12877_3 (m.d 0 3) (by simp) with h12888 | h12888
                                      · linarith only [h12888, h4, hlam]
                                      · rcases p12877_3 (m.d 1 3) (by simp) with h12890 | h12890
                                        · linarith only [h12835, h12890, hlam]
                                        · rcases p12877_3 (m.d 2 3) (by simp) with h12892 | h12892
                                          · rcases p12877_3 (m.d 3 4) (by simp) with h12893 | h12893
                                            · linarith only [h12846, h12893, hlam]
                                            · linarith only [h10361, h12893, hlam]
                                          · linarith only [h12892, h4, hlam]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      rcases p12877_3 (m.d 0 3) (by simp) with h12897 | h12897
                                      · linarith only [h12897, h4, hlam]
                                      · linarith only [h1, h12897, hlam]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h1, h12604, h12835, h12849, hc12, hc23, hlam, hphi, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h1, h12604, h12835, hc12, hc23, hlam, hphi, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h1, h12835, h12846, hc12, hc23, hlam, hphi, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12835, h12846, hc12, hc23, hlam, hphi, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12846, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h1, h12604, h12835, h12846, hc12, hc23, hlam, hphi, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h1, h12835, h12847, hc12, hc23, hlam, hphi, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12835, h12847, hc12, hc23, hlam, hphi, p12877_1]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12847, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [h12849, hlam, p12877_0]
                                    · have p12877_0 := h12877c.1
                                      have p12877_1 := h12877c.2.1
                                      have p12877_2 := h12877c.2.2.1
                                      have p12877_3 := h12877c.2.2.2
                                      linarith only [hlam, p12877_0]
                          · linarith only [h12868, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          rcases p12850_3 (m.d 0 1) (by simp) with h12914 | h12914
                          · rcases p12850_3 (m.d 1 2) (by simp) with h12915 | h12915
                            · linarith only [h0, h12915, hlam]
                            · rcases p12850_3 (m.d 1 3) (by simp) with h12917 | h12917
                              · linarith only [h1, h12917, hlam]
                              · rcases p12850_3 (m.d 1 4) (by simp) with h12919 | h12919
                                · linarith only [h12919, h2, hlam]
                                · linarith only [h12845, h12919, hlam]
                          · linarith only [h12914, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h0, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12835, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12837, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12839, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h1, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h1, h10361, h12846, hc12, hc23, hlam, hphi, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12841, hlam, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12843, hlam, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h2, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h10361, h12846, h2, hc12, hc23, hlam, hphi, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h10361, h12835, h12846, h2, hc12, hc23, hlam, hphi, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h10361, h12835, h12843, h12846, h2, hc12, hc23, hlam, hphi, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h3, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12604, h12846, h12849, h3, hc12, hc23, hlam, hphi, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12604, h12835, h12846, h12849, h3, hc12, hc23, hlam, hphi, p12850_1]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [h12845, hlam, p12850_0]
                        · have p12850_0 := h12850c.1
                          have p12850_1 := h12850c.2.1
                          have p12850_2 := h12850c.2.2.1
                          have p12850_3 := h12850c.2.2.2
                          linarith only [hlam, p12850_0]
                      · linarith only [h10361, h12834, h12849, hlam]
                    · linarith only [h0, h12845, h12848, h2, h8674, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1, h10361, h12835, h12846, h12847, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12946 | h12946
                  · linarith only [h1, h12604, h12835, h12846, h12946, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12948 | h12948
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12949 | h12949
                      · rcases h1bigk with h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c | h12950c
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h12952 | h12952
                          · rcases p12950_3 (m.d 1 2) (by simp) with h12953 | h12953
                            · linarith only [h12953, hlam, p12950_0]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h12955 | h12955
                              · linarith only [h1, h12955, hlam]
                              · linarith only [h12835, h12955, hlam]
                          · linarith only [h12952, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h12959 | h12959
                          · rcases p12950_3 (m.d 1 2) (by simp) with h12960 | h12960
                            · linarith only [h0, h12960, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h12962 | h12962
                              · linarith only [h12962, hlam, p12950_0]
                              · rcases p12950_3 (m.d 1 4) (by simp) with h12964 | h12964
                                · linarith only [h12964, h2, hlam]
                                · linarith only [h12841, h12964, hlam]
                          · linarith only [h12959, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h12968 | h12968
                          · rcases p12950_3 (m.d 1 2) (by simp) with h12969 | h12969
                            · linarith only [h0, h12969, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h12971 | h12971
                              · linarith only [h1, h12971, hlam]
                              · rcases p12950_3 (m.d 1 4) (by simp) with h12973 | h12973
                                · linarith only [h12973, hlam, p12950_0]
                                · rcases p12950_3 (m.d 1 5) (by simp) with h12975 | h12975
                                  · linarith only [h12975, h3, hlam]
                                  · rcases h3bigk with h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12835, h12946, h12949, h4, hc12, hc34, hlam, hphi, ht23, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h4, hlam, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h10361, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12604, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h1, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12835, hlam, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12841, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12843, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12946, h12949, hc03, hc34, hlam, hphi, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12835, h12946, h12949, hc12, hc34, hlam, hphi, ht23, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12846, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12946, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      rcases p12977_3 (m.d 0 3) (by simp) with h12993 | h12993
                                      · linarith only [h12993, hlam, p12977_0]
                                      · rcases p12977_3 (m.d 1 3) (by simp) with h12995 | h12995
                                        · linarith only [h12841, h12995, hlam]
                                        · rcases p12977_3 (m.d 2 3) (by simp) with h12997 | h12997
                                          · linarith only [h12846, h12997, hlam]
                                          · linarith only [h12997, h4, hlam]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      rcases p12977_3 (m.d 0 3) (by simp) with h13000 | h13000
                                      · linarith only [h10361, h13000, hlam]
                                      · linarith only [h1, h13000, hlam]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h1, h12604, h12835, hc12, hc34, hlam, hphi, ht23, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      rcases p12977_3 (m.d 0 3) (by simp) with h13006 | h13006
                                      · linarith only [h13006, hlam, p12977_0]
                                      · rcases p12977_3 (m.d 1 3) (by simp) with h13008 | h13008
                                        · linarith only [h12843, h13008, hlam]
                                        · rcases p12977_3 (m.d 2 3) (by simp) with h13010 | h13010
                                          · linarith only [h12946, h13010, hlam]
                                          · linarith only [h13010, h4, hlam]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      rcases p12977_3 (m.d 0 3) (by simp) with h13013 | h13013
                                      · linarith only [h12604, h13013, hlam]
                                      · linarith only [h1, h13013, hlam]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p12977_1]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [h12949, hlam, p12977_0]
                                    · have p12977_0 := h12977c.1
                                      have p12977_1 := h12977c.2.1
                                      have p12977_2 := h12977c.2.2.1
                                      have p12977_3 := h12977c.2.2.2
                                      linarith only [hlam, p12977_0]
                          · linarith only [h12968, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h13020 | h13020
                          · rcases p12950_3 (m.d 1 2) (by simp) with h13021 | h13021
                            · linarith only [h0, h13021, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h13023 | h13023
                              · linarith only [h1, h13023, hlam]
                              · rcases p12950_3 (m.d 1 4) (by simp) with h13025 | h13025
                                · linarith only [h13025, h2, hlam]
                                · linarith only [h12845, h13025, hlam]
                          · linarith only [h13020, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h0, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h12835, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h12837, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h12839, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h1, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h1, h10361, hc12, hc34, hlam, hphi, ht23, p12950_1]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h12841, hlam, p12950_1]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h12843, hlam, p12950_1]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h2, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h13040 | h13040
                          · rcases p12950_3 (m.d 1 2) (by simp) with h13041 | h13041
                            · linarith only [h12837, h13041, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h13043 | h13043
                              · linarith only [h12841, h13043, hlam]
                              · linarith only [h12835, h13043, hlam]
                          · linarith only [h0, h13040, hlam]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h13047 | h13047
                          · rcases p12950_3 (m.d 1 2) (by simp) with h13048 | h13048
                            · linarith only [h12837, h13048, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h13050 | h13050
                              · linarith only [h12841, h13050, hlam]
                              · rcases p12950_3 (m.d 1 4) (by simp) with h13052 | h13052
                                · rcases p12950_3 (m.d 1 5) (by simp) with h13053 | h13053
                                  · linarith only [h12845, h13053, hlam]
                                  · linarith only [h12843, h13053, hlam]
                                · linarith only [h12841, h13052, hlam]
                          · linarith only [h1, h13047, hlam]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h13059 | h13059
                          · rcases p12950_3 (m.d 1 2) (by simp) with h13060 | h13060
                            · linarith only [h12837, h13060, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h13062 | h13062
                              · linarith only [h12841, h13062, hlam]
                              · rcases p12950_3 (m.d 1 4) (by simp) with h13064 | h13064
                                · rcases p12950_3 (m.d 1 5) (by simp) with h13065 | h13065
                                  · linarith only [h12845, h13065, hlam]
                                  · rcases h3bigk with h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c | h13067c
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12835, h12946, h12949, h4, hc12, hc34, hlam, hphi, ht23, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h4, hlam, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h10361, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12604, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h1, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12835, hlam, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12841, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12843, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12946, h12949, hc03, hc34, hlam, hphi, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12835, h12946, h12949, hc12, hc34, hlam, hphi, ht23, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12846, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12946, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      rcases p13067_3 (m.d 0 3) (by simp) with h13083 | h13083
                                      · linarith only [h13083, hlam, p13067_0]
                                      · rcases p13067_3 (m.d 1 3) (by simp) with h13085 | h13085
                                        · linarith only [h12841, h13085, hlam]
                                        · rcases p13067_3 (m.d 2 3) (by simp) with h13087 | h13087
                                          · linarith only [h12846, h13087, hlam]
                                          · linarith only [h13087, h4, hlam]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      rcases p13067_3 (m.d 0 3) (by simp) with h13090 | h13090
                                      · linarith only [h10361, h13090, hlam]
                                      · linarith only [h1, h13090, hlam]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h1, h12604, h12835, hc12, hc34, hlam, hphi, ht23, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      rcases p13067_3 (m.d 0 3) (by simp) with h13096 | h13096
                                      · linarith only [h13096, hlam, p13067_0]
                                      · rcases p13067_3 (m.d 1 3) (by simp) with h13098 | h13098
                                        · linarith only [h12843, h13098, hlam]
                                        · rcases p13067_3 (m.d 2 3) (by simp) with h13100 | h13100
                                          · linarith only [h12946, h13100, hlam]
                                          · linarith only [h13100, h4, hlam]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      rcases p13067_3 (m.d 0 3) (by simp) with h13103 | h13103
                                      · linarith only [h12604, h13103, hlam]
                                      · linarith only [h1, h13103, hlam]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p13067_1]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [h12949, hlam, p13067_0]
                                    · have p13067_0 := h13067c.1
                                      have p13067_1 := h13067c.2.1
                                      have p13067_2 := h13067c.2.2.1
                                      have p13067_3 := h13067c.2.2.2
                                      linarith only [hlam, p13067_0]
                                · linarith only [h12845, h13064, hlam]
                          · linarith only [h13059, h3, hlam]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h3, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h13112 | h13112
                          · rcases p12950_3 (m.d 1 2) (by simp) with h13113 | h13113
                            · linarith only [h12839, h13113, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h13115 | h13115
                              · linarith only [h12843, h13115, hlam]
                              · linarith only [h12835, h13115, hlam]
                          · linarith only [h0, h13112, hlam]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          rcases p12950_3 (m.d 0 1) (by simp) with h13119 | h13119
                          · rcases p12950_3 (m.d 1 2) (by simp) with h13120 | h13120
                            · linarith only [h12839, h13120, hlam]
                            · rcases p12950_3 (m.d 1 3) (by simp) with h13122 | h13122
                              · linarith only [h12843, h13122, hlam]
                              · rcases p12950_3 (m.d 1 4) (by simp) with h13124 | h13124
                                · rcases p12950_3 (m.d 1 5) (by simp) with h13125 | h13125
                                  · rcases h3bigk with h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c | h13126c
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h10361, h12835, hc12, hc34, hlam, hphi, ht23, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h4, hlam, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h10361, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12604, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h1, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12835, hlam, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12841, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12843, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12846, hc03, hc34, hlam, hphi, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12835, h12846, hc12, hc34, hlam, hphi, ht23, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12846, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12946, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      rcases p13126_3 (m.d 0 3) (by simp) with h13142 | h13142
                                      · linarith only [h13142, hlam, p13126_0]
                                      · rcases p13126_3 (m.d 1 3) (by simp) with h13144 | h13144
                                        · linarith only [h12841, h13144, hlam]
                                        · rcases p13126_3 (m.d 2 3) (by simp) with h13146 | h13146
                                          · linarith only [h12846, h13146, hlam]
                                          · linarith only [h13146, h4, hlam]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      rcases p13126_3 (m.d 0 3) (by simp) with h13149 | h13149
                                      · linarith only [h10361, h13149, hlam]
                                      · linarith only [h1, h13149, hlam]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h1, h12604, h12835, hc12, hc34, hlam, hphi, ht23, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      rcases p13126_3 (m.d 0 3) (by simp) with h13155 | h13155
                                      · linarith only [h13155, hlam, p13126_0]
                                      · rcases p13126_3 (m.d 1 3) (by simp) with h13157 | h13157
                                        · linarith only [h12843, h13157, hlam]
                                        · rcases p13126_3 (m.d 2 3) (by simp) with h13159 | h13159
                                          · linarith only [h12946, h13159, hlam]
                                          · linarith only [h13159, h4, hlam]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      rcases p13126_3 (m.d 0 3) (by simp) with h13162 | h13162
                                      · linarith only [h12604, h13162, hlam]
                                      · linarith only [h1, h13162, hlam]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p13126_1]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [h12949, hlam, p13126_0]
                                    · have p13126_0 := h13126c.1
                                      have p13126_1 := h13126c.2.1
                                      have p13126_2 := h13126c.2.2.1
                                      have p13126_3 := h13126c.2.2.2
                                      linarith only [hlam, p13126_0]
                                  · linarith only [h12843, h13125, hlam]
                                · linarith only [h12841, h13124, hlam]
                          · linarith only [h1, h13119, hlam]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [h12845, hlam, p12950_0]
                        · have p12950_0 := h12950c.1
                          have p12950_1 := h12950c.2.1
                          have p12950_2 := h12950c.2.2.1
                          have p12950_3 := h12950c.2.2.2
                          linarith only [hlam, p12950_0]
                      · linarith only [h12834, h12846, h12949, h8674, hlam]
                    · linarith only [h12845, h12948, h2, h8674, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13175 | h13175
                · linarith only [h10361, h12834, h12837, h12845, h13175, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13177 | h13177
                  · linarith only [h1, h12604, h12835, h13175, h13177, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13179 | h13179
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13180 | h13180
                      · rcases h1bigk with h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c | h13181c
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          rcases p13181_3 (m.d 0 1) (by simp) with h13183 | h13183
                          · rcases p13181_3 (m.d 1 2) (by simp) with h13184 | h13184
                            · linarith only [h13184, hlam, p13181_0]
                            · rcases p13181_3 (m.d 1 3) (by simp) with h13186 | h13186
                              · linarith only [h1, h13186, hlam]
                              · linarith only [h12835, h13186, hlam]
                          · linarith only [h13183, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          rcases p13181_3 (m.d 0 1) (by simp) with h13190 | h13190
                          · rcases p13181_3 (m.d 1 2) (by simp) with h13191 | h13191
                            · linarith only [h0, h13191, hlam]
                            · rcases p13181_3 (m.d 1 3) (by simp) with h13193 | h13193
                              · linarith only [h13193, hlam, p13181_0]
                              · rcases p13181_3 (m.d 1 4) (by simp) with h13195 | h13195
                                · linarith only [h13195, h2, hlam]
                                · linarith only [h12841, h13195, hlam]
                          · linarith only [h13190, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          rcases p13181_3 (m.d 0 1) (by simp) with h13199 | h13199
                          · rcases p13181_3 (m.d 1 2) (by simp) with h13200 | h13200
                            · linarith only [h0, h13200, hlam]
                            · rcases p13181_3 (m.d 1 3) (by simp) with h13202 | h13202
                              · linarith only [h1, h13202, hlam]
                              · rcases p13181_3 (m.d 1 4) (by simp) with h13204 | h13204
                                · linarith only [h13204, hlam, p13181_0]
                                · rcases p13181_3 (m.d 1 5) (by simp) with h13206 | h13206
                                  · linarith only [h13206, h3, hlam]
                                  · linarith only [h12845, h13206, hlam]
                          · linarith only [h13199, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          rcases p13181_3 (m.d 0 1) (by simp) with h13210 | h13210
                          · rcases p13181_3 (m.d 1 2) (by simp) with h13211 | h13211
                            · linarith only [h0, h13211, hlam]
                            · rcases p13181_3 (m.d 1 3) (by simp) with h13213 | h13213
                              · linarith only [h1, h13213, hlam]
                              · rcases p13181_3 (m.d 1 4) (by simp) with h13215 | h13215
                                · linarith only [h13215, h2, hlam]
                                · rcases p13181_3 (m.d 1 5) (by simp) with h13217 | h13217
                                  · linarith only [h13217, hlam, p13181_0]
                                  · rcases h3bigk with h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c | h13219c
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h12835, h13177, h13180, h4, hc12, hc34, hlam, hphi, ht23, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h4, hlam, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h10361, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h12604, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h1, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h12835, hlam, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h12841, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h12843, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h13177, h13180, hc03, hc34, hlam, hphi, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h12835, h13177, h13180, hc12, hc34, hlam, hphi, ht23, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h13175, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h13177, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      rcases p13219_3 (m.d 0 3) (by simp) with h13235 | h13235
                                      · linarith only [h13235, hlam, p13219_0]
                                      · rcases p13219_3 (m.d 1 3) (by simp) with h13237 | h13237
                                        · linarith only [h12841, h13237, hlam]
                                        · rcases p13219_3 (m.d 2 3) (by simp) with h13239 | h13239
                                          · linarith only [h13175, h13239, hlam]
                                          · linarith only [h13239, h4, hlam]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      rcases p13219_3 (m.d 0 3) (by simp) with h13242 | h13242
                                      · linarith only [h10361, h13242, hlam]
                                      · linarith only [h1, h13242, hlam]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h1, h12604, h12835, hc12, hc34, hlam, hphi, ht23, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      rcases p13219_3 (m.d 0 3) (by simp) with h13248 | h13248
                                      · linarith only [h13248, hlam, p13219_0]
                                      · rcases p13219_3 (m.d 1 3) (by simp) with h13250 | h13250
                                        · linarith only [h12843, h13250, hlam]
                                        · rcases p13219_3 (m.d 2 3) (by simp) with h13252 | h13252
                                          · linarith only [h13177, h13252, hlam]
                                          · linarith only [h13252, h4, hlam]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      rcases p13219_3 (m.d 0 3) (by simp) with h13255 | h13255
                                      · linarith only [h12604, h13255, hlam]
                                      · linarith only [h1, h13255, hlam]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p13219_1]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [h13180, hlam, p13219_0]
                                    · have p13219_0 := h13219c.1
                                      have p13219_1 := h13219c.2.1
                                      have p13219_2 := h13219c.2.2.1
                                      have p13219_3 := h13219c.2.2.2
                                      linarith only [hlam, p13219_0]
                          · linarith only [h13210, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h0, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12835, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12837, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12839, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h1, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h1, h10361, hc12, hc34, hlam, hphi, ht23, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12841, hlam, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12843, hlam, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h2, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12834, h12845, h13175, h8674, hc12, hc34, hlam, hphi, ht23, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12834, h12845, h13175, h8674, hc13, hc34, hlam, hphi, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12845, hlam, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h3, hlam, p13181_0]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12834, h12845, h13175, h8674, hc12, hc34, hlam, hphi, ht23, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12834, h12835, h12845, h13175, h8674, hc12, hc34, hlam, hphi, ht23, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [h12834, h12837, h12845, h13175, h8674, hc12, hc34, hlam, hphi, ht23, p13181_1]
                        · have p13181_0 := h13181c.1
                          have p13181_1 := h13181c.2.1
                          have p13181_2 := h13181c.2.2.1
                          have p13181_3 := h13181c.2.2.2
                          linarith only [hlam, p13181_0]
                      · linarith only [h12834, h13175, h13180, h8674, hlam]
                    · linarith only [h12834, h13179, h8674, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h13284 | h13284
    · linarith only [h0, h13284, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h13286 | h13286
      · linarith only [h0, h13286, h8674, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13288 | h13288
        · linarith only [h0, h13288, h9870, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13290 | h13290
          · linarith only [h1, h10361, h13290, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13292 | h13292
            · linarith only [h1, h12604, h13292, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13294 | h13294
              · linarith only [h12834, h13294, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13296 | h13296
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13297 | h13297
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13298 | h13298
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13299 | h13299
                      · linarith only [h0, h10361, h12834, h13296, h13299, h4, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h10361, h13298, h13299, h4, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13302 | h13302
                      · linarith only [h0, h13298, h13302, h8674, hc12, hc34, hlam, hphi, ht23]
                      · rcases h1bigk with h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c | h13304c
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          rcases p13304_3 (m.d 0 1) (by simp) with h13306 | h13306
                          · rcases p13304_3 (m.d 1 2) (by simp) with h13307 | h13307
                            · linarith only [h13307, hlam, p13304_0]
                            · rcases p13304_3 (m.d 1 3) (by simp) with h13309 | h13309
                              · linarith only [h1, h13309, hlam]
                              · linarith only [h13284, h13309, hlam]
                          · linarith only [h13306, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          rcases p13304_3 (m.d 0 1) (by simp) with h13313 | h13313
                          · rcases p13304_3 (m.d 1 2) (by simp) with h13314 | h13314
                            · linarith only [h0, h13314, hlam]
                            · rcases p13304_3 (m.d 1 3) (by simp) with h13316 | h13316
                              · linarith only [h13316, hlam, p13304_0]
                              · rcases p13304_3 (m.d 1 4) (by simp) with h13318 | h13318
                                · linarith only [h13318, h2, hlam]
                                · linarith only [h13290, h13318, hlam]
                          · linarith only [h13313, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          rcases p13304_3 (m.d 0 1) (by simp) with h13322 | h13322
                          · rcases p13304_3 (m.d 1 2) (by simp) with h13323 | h13323
                            · linarith only [h0, h13323, hlam]
                            · rcases p13304_3 (m.d 1 3) (by simp) with h13325 | h13325
                              · linarith only [h1, h13325, hlam]
                              · rcases p13304_3 (m.d 1 4) (by simp) with h13327 | h13327
                                · linarith only [h13327, hlam, p13304_0]
                                · rcases p13304_3 (m.d 1 5) (by simp) with h13329 | h13329
                                  · linarith only [h13329, h3, hlam]
                                  · linarith only [h13294, h13329, hlam]
                          · linarith only [h13322, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          rcases p13304_3 (m.d 0 1) (by simp) with h13333 | h13333
                          · rcases p13304_3 (m.d 1 2) (by simp) with h13334 | h13334
                            · linarith only [h0, h13334, hlam]
                            · rcases p13304_3 (m.d 1 3) (by simp) with h13336 | h13336
                              · linarith only [h1, h13336, hlam]
                              · rcases p13304_3 (m.d 1 4) (by simp) with h13338 | h13338
                                · linarith only [h13338, h2, hlam]
                                · rcases p13304_3 (m.d 1 5) (by simp) with h13340 | h13340
                                  · linarith only [h13340, hlam, p13304_0]
                                  · rcases h3bigk with h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h10361, hc13, hc34, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h4, hlam, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h10361, hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h12604, hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h1, hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13284, hlam, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13290, hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13292, hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      rcases p13342_3 (m.d 0 3) (by simp) with h13353 | h13353
                                      · linarith only [h13353, h4, hlam]
                                      · rcases p13342_3 (m.d 1 3) (by simp) with h13355 | h13355
                                        · linarith only [h13284, h13355, hlam]
                                        · rcases p13342_3 (m.d 2 3) (by simp) with h13357 | h13357
                                          · rcases p13342_3 (m.d 3 4) (by simp) with h13358 | h13358
                                            · linarith only [h13296, h13358, hlam]
                                            · linarith only [h10361, h13358, hlam]
                                          · linarith only [h13357, h4, hlam]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      rcases p13342_3 (m.d 0 3) (by simp) with h13362 | h13362
                                      · linarith only [h13362, h4, hlam]
                                      · linarith only [h1, h13362, hlam]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h10361, h4, hc02, hc23, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h0, h10361, h13302, h4, hc12, hc23, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h0, h13296, h4, hc12, hc23, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13284, h13296, hc12, hc23, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13296, hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13302, hlam, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h0, h13297, h4, hc12, hc23, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13284, h13297, hc12, hc23, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h13297, hlam, p13342_0]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [h0, h10361, h13297, h4, hc12, hc25, hlam, hphi, p13342_1]
                                    · have p13342_0 := h13342c.1
                                      have p13342_1 := h13342c.2.1
                                      have p13342_2 := h13342c.2.2.1
                                      have p13342_3 := h13342c.2.2.2
                                      linarith only [hlam, p13342_0]
                          · linarith only [h13333, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h0, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13284, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13286, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13288, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h1, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h1, h10361, hc12, hc34, hlam, hphi, ht23, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13290, hlam, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13292, hlam, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h2, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13298, h2, h8674, hc12, hc45, hlam, hphi, ht23, ht34, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13298, h2, h8674, hc13, hc45, hlam, hphi, ht34, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h13294, hlam, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h3, hlam, p13304_0]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h12604, h13297, h3, hc12, hc23, hlam, hphi, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h12604, h13284, h13297, h3, hc12, hc23, hlam, hphi, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [h12604, h13286, h13297, h3, hc12, hc23, hlam, hphi, p13304_1]
                        · have p13304_0 := h13304c.1
                          have p13304_1 := h13304c.2.1
                          have p13304_2 := h13304c.2.2.1
                          have p13304_3 := h13304c.2.2.2
                          linarith only [hlam, p13304_0]
                  · linarith only [h1, h10361, h13284, h13296, h13297, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13400 | h13400
                  · linarith only [h1, h12604, h13284, h13296, h13400, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13402 | h13402
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13403 | h13403
                      · rcases h1bigk with h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c | h13404c
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          rcases p13404_3 (m.d 0 1) (by simp) with h13406 | h13406
                          · rcases p13404_3 (m.d 1 2) (by simp) with h13407 | h13407
                            · linarith only [h13407, hlam, p13404_0]
                            · rcases p13404_3 (m.d 1 3) (by simp) with h13409 | h13409
                              · linarith only [h1, h13409, hlam]
                              · linarith only [h13284, h13409, hlam]
                          · linarith only [h13406, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          rcases p13404_3 (m.d 0 1) (by simp) with h13413 | h13413
                          · rcases p13404_3 (m.d 1 2) (by simp) with h13414 | h13414
                            · linarith only [h0, h13414, hlam]
                            · rcases p13404_3 (m.d 1 3) (by simp) with h13416 | h13416
                              · linarith only [h13416, hlam, p13404_0]
                              · rcases p13404_3 (m.d 1 4) (by simp) with h13418 | h13418
                                · linarith only [h13418, h2, hlam]
                                · linarith only [h13290, h13418, hlam]
                          · linarith only [h13413, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          rcases p13404_3 (m.d 0 1) (by simp) with h13422 | h13422
                          · rcases p13404_3 (m.d 1 2) (by simp) with h13423 | h13423
                            · linarith only [h0, h13423, hlam]
                            · rcases p13404_3 (m.d 1 3) (by simp) with h13425 | h13425
                              · linarith only [h1, h13425, hlam]
                              · rcases p13404_3 (m.d 1 4) (by simp) with h13427 | h13427
                                · linarith only [h13427, hlam, p13404_0]
                                · rcases p13404_3 (m.d 1 5) (by simp) with h13429 | h13429
                                  · linarith only [h13429, h3, hlam]
                                  · linarith only [h13294, h13429, hlam]
                          · linarith only [h13422, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          rcases p13404_3 (m.d 0 1) (by simp) with h13433 | h13433
                          · rcases p13404_3 (m.d 1 2) (by simp) with h13434 | h13434
                            · linarith only [h0, h13434, hlam]
                            · rcases p13404_3 (m.d 1 3) (by simp) with h13436 | h13436
                              · linarith only [h1, h13436, hlam]
                              · rcases p13404_3 (m.d 1 4) (by simp) with h13438 | h13438
                                · linarith only [h13438, h2, hlam]
                                · rcases p13404_3 (m.d 1 5) (by simp) with h13440 | h13440
                                  · linarith only [h13440, hlam, p13404_0]
                                  · rcases h3bigk with h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c | h13442c
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13284, h13400, h13403, h4, hc12, hc34, hlam, hphi, ht23, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h4, hlam, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h10361, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h12604, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h1, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13284, hlam, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13290, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13292, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13400, h13403, hc03, hc34, hlam, hphi, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13284, h13400, h13403, hc12, hc34, hlam, hphi, ht23, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13296, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13400, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      rcases p13442_3 (m.d 0 3) (by simp) with h13458 | h13458
                                      · linarith only [h13458, hlam, p13442_0]
                                      · rcases p13442_3 (m.d 1 3) (by simp) with h13460 | h13460
                                        · linarith only [h13290, h13460, hlam]
                                        · rcases p13442_3 (m.d 2 3) (by simp) with h13462 | h13462
                                          · linarith only [h13296, h13462, hlam]
                                          · linarith only [h13462, h4, hlam]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      rcases p13442_3 (m.d 0 3) (by simp) with h13465 | h13465
                                      · linarith only [h10361, h13465, hlam]
                                      · linarith only [h1, h13465, hlam]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h1, h12604, h13284, hc12, hc34, hlam, hphi, ht23, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      rcases p13442_3 (m.d 0 3) (by simp) with h13471 | h13471
                                      · linarith only [h13471, hlam, p13442_0]
                                      · rcases p13442_3 (m.d 1 3) (by simp) with h13473 | h13473
                                        · linarith only [h13292, h13473, hlam]
                                        · rcases p13442_3 (m.d 2 3) (by simp) with h13475 | h13475
                                          · linarith only [h13400, h13475, hlam]
                                          · linarith only [h13475, h4, hlam]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      rcases p13442_3 (m.d 0 3) (by simp) with h13478 | h13478
                                      · linarith only [h12604, h13478, hlam]
                                      · linarith only [h1, h13478, hlam]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p13442_1]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [h13403, hlam, p13442_0]
                                    · have p13442_0 := h13442c.1
                                      have p13442_1 := h13442c.2.1
                                      have p13442_2 := h13442c.2.2.1
                                      have p13442_3 := h13442c.2.2.2
                                      linarith only [hlam, p13442_0]
                          · linarith only [h13433, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h0, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h13284, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h13286, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h13288, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h1, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h12834, h13290, h13296, h13402, h2, hc12, hc34, hlam, hphi, ht23, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h13290, hlam, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h13292, hlam, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h2, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h12834, h13296, h13402, h2, hc12, hc34, hlam, hphi, ht23, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h12834, h13296, h13402, h2, hc13, hc34, hlam, hphi, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h13294, hlam, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h3, hlam, p13404_0]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h12834, h13296, h13402, h3, hc12, hc34, hlam, hphi, ht23, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h12834, h13284, h13296, h13402, h3, hc12, hc34, hlam, hphi, ht23, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [h12834, h13286, h13296, h13402, h3, hc12, hc34, hlam, hphi, ht23, p13404_1]
                        · have p13404_0 := h13404c.1
                          have p13404_1 := h13404c.2.1
                          have p13404_2 := h13404c.2.2.1
                          have p13404_3 := h13404c.2.2.2
                          linarith only [hlam, p13404_0]
                      · linarith only [h13296, h13402, h13403, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13506 | h13506
                      · linarith only [h0, h13296, h13402, h13506, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h13296, h13506, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 0 3 5 (by decide) (by decide) with h12604 | h12604
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h12604
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h12604

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 0 3 4 (by decide) (by decide) with h10361 | h10361
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361

end R2N4
