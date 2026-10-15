import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13698000 in
set_option maxHeartbeats 13698000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s11 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  rcases m.htr 0 1 4 (by decide) (by decide) with h8836 | h8836
  · rcases m.htr 0 1 5 (by decide) (by decide) with h8837 | h8837
    · rcases m.htr 0 2 3 (by decide) (by decide) with h8838 | h8838
      · rcases m.htr 0 2 4 (by decide) (by decide) with h8839 | h8839
        · rcases m.htr 0 2 5 (by decide) (by decide) with h8840 | h8840
          · rcases m.htr 0 3 4 (by decide) (by decide) with h8841 | h8841
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8842 | h8842
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8843 | h8843
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8844 | h8844
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8845 | h8845
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8846 | h8846
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8847 | h8847
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h8848 | h8848
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8849 | h8849
                            · linarith only [h7600, h8836, h8849, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8851 | h8851
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8852 | h8852
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h8853 | h8853
                                  · linarith only [h8845, h8849, h8853, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8855 | h8855
                                    · linarith only [h8845, h8849, h8851, h8855, hlam]
                                    · rcases h0bigk with h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c | h8857c
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h0, hlam, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h7600, hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h7600, h8843, h8844, h8845, h8849, h8851, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h7600, h8844, hc12, hlam, hphi, ht01, ht0b, ht5b, p8857_1, u5ehi0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h0, h8836, h8843, h8845, h8849, h8851, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h0, h7600, h8836, h8843, h8845, h8849, h8851, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h0, h8843, h8845, h8849, h8851, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        rcases p8857_3 (m.d 0 1) (by simp) with h8867 | h8867
                                        · linarith only [h0, h8867, hlam]
                                        · linarith only [h8837, h8867, hlam]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8836, h8843, h8845, h8849, h8851, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8838, hlam, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h7600, h8843, h8844, h8845, h8849, h8851, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        rcases p8857_3 (m.d 0 1) (by simp) with h8874 | h8874
                                        · linarith only [h7600, h8874, hlam]
                                        · linarith only [h8837, h8874, hlam]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8836, hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8839, hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8841, hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h0, h8836, h8843, h8845, h8849, h8851, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8837, hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8840, hlam, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8842, hlam, p8857_0]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [h8843, hlam, p8857_1]
                                      · have p8857_0 := h8857c.1
                                        have p8857_1 := h8857c.2.1
                                        have p8857_2 := h8857c.2.2.1
                                        have p8857_3 := h8857c.2.2.2
                                        linarith only [hlam, p8857_0]
                                · linarith only [h7600, h8836, h8843, h8844, h8848, h8849, h8851, h8852, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7600, h8836, h8843, h8844, h8847, h8849, h8851, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7600, h8836, h8843, h8848, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h7600, h8836, h8843, h8847, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h7600, h8836, h8843, h8844, h8846, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h7600, h8836, h8843, h8844, h8845, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h8836, h8843, h8844, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8894 | h8894
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h8895 | h8895
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h8896 | h8896
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h8897 | h8897
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h8898 | h8898
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8899 | h8899
                            · linarith only [h7600, h8836, h8843, h8894, h8899, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8901 | h8901
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8902 | h8902
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h8903 | h8903
                                  · linarith only [h8836, h8843, h8895, h8903, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8905 | h8905
                                    · linarith only [h8838, h8843, h8901, h8905, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c | h8907c
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h0, hlam, p8907_1]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h7600, hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        rcases p8907_3 (m.d 0 1) (by simp) with h8911 | h8911
                                        · rcases p8907_3 (m.d 0 2) (by simp) with h8912 | h8912
                                          · rcases p8907_3 (m.d 0 3) (by simp) with h8913 | h8913
                                            · rcases p8907_3 (m.d 0 4) (by simp) with h8914 | h8914
                                              · linarith only [h8836, h8914, hlam]
                                              · rcases p8907_3 (m.d 0 5) (by simp) with h8916 | h8916
                                                · linarith only [h8837, h8916, hlam]
                                                · linarith only [h8843, h8916, hlam]
                                            · linarith only [h8841, h8913, hlam]
                                          · linarith only [h8839, h8912, hlam]
                                        · linarith only [h8836, h8911, hlam]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h7600, h8894, hc12, hlam, hphi, ht01, ht0b, ht5b, p8907_1, u5ehi0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h0, h8837, h8896, h8902, hc12, hlam, hphi, ht01, ht0b, ht5b, p8907_1, u5ehi3]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h0, h7600, h8837, h8896, h8902, hc12, hlam, hphi, ht01, ht0b, ht5b, p8907_1, u5ehi3]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        rcases p8907_3 (m.d 0 1) (by simp) with h8926 | h8926
                                        · linarith only [h0, h8926, hlam]
                                        · linarith only [h8836, h8926, hlam]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        rcases p8907_3 (m.d 0 1) (by simp) with h8929 | h8929
                                        · linarith only [h0, h8929, hlam]
                                        · linarith only [h8837, h8929, hlam]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8837, h8896, h8902, hc03, hlam, hphi, ht0b, ht5b, p8907_1, u5ehi3]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8838, hlam, p8907_1]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        rcases p8907_3 (m.d 0 1) (by simp) with h8935 | h8935
                                        · linarith only [h7600, h8935, hlam]
                                        · linarith only [h8836, h8935, hlam]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        rcases p8907_3 (m.d 0 1) (by simp) with h8938 | h8938
                                        · linarith only [h7600, h8938, hlam]
                                        · linarith only [h8837, h8938, hlam]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8836, hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8839, hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8841, hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8843, hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8837, hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8840, hlam, p8907_1]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [h8842, hlam, p8907_0]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        rcases p8907_3 (m.d 0 1) (by simp) with h8949 | h8949
                                        · rcases p8907_3 (m.d 0 2) (by simp) with h8950 | h8950
                                          · rcases p8907_3 (m.d 0 3) (by simp) with h8951 | h8951
                                            · rcases p8907_3 (m.d 0 4) (by simp) with h8952 | h8952
                                              · linarith only [h8843, h8952, hlam]
                                              · rcases p8907_3 (m.d 0 5) (by simp) with h8954 | h8954
                                                · rcases h2bigk with h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c | h8955c
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h0, hlam, p8955_1]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h0, h8902, hc12, hlam, hphi, ht01, ht0b, ht5b, p8955_1, u5ehi3]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    rcases p8955_3 (m.d 0 2) (by simp) with h8959 | h8959
                                                    · rcases p8955_3 (m.d 1 2) (by simp) with h8960 | h8960
                                                      · rcases p8955_3 (m.d 2 3) (by simp) with h8961 | h8961
                                                        · linarith only [h8838, h8961, hlam]
                                                        · linarith only [h8901, h8961, hlam]
                                                      · linarith only [h8895, h8960, hlam]
                                                    · linarith only [h8959, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    rcases p8955_3 (m.d 0 2) (by simp) with h8966 | h8966
                                                    · rcases p8955_3 (m.d 1 2) (by simp) with h8967 | h8967
                                                      · rcases p8955_3 (m.d 2 3) (by simp) with h8968 | h8968
                                                        · linarith only [h8838, h8968, hlam]
                                                        · linarith only [h8902, h8968, hlam]
                                                      · linarith only [h8896, h8967, hlam]
                                                    · linarith only [h8966, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h0, h8837, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p8907_1, p8955_1]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8902, hc12, hlam, hphi, ht01, ht0b, ht5b, p8955_1, u5ehi3]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h0, h8836, h8837, h8895, hlam, p8907_1, p8955_2]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    rcases p8955_3 (m.d 0 2) (by simp) with h8977 | h8977
                                                    · linarith only [h0, h8977, hlam]
                                                    · linarith only [h8840, h8977, hlam]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8838, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8894, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    rcases p8955_3 (m.d 0 2) (by simp) with h8983 | h8983
                                                    · rcases p8955_3 (m.d 1 2) (by simp) with h8984 | h8984
                                                      · rcases p8955_3 (m.d 2 3) (by simp) with h8985 | h8985
                                                        · rcases p8955_3 (m.d 2 4) (by simp) with h8986 | h8986
                                                          · linarith only [h8901, h8986, hlam]
                                                          · rcases p8955_3 (m.d 2 5) (by simp) with h8988 | h8988
                                                            · linarith only [h8902, h8988, hlam]
                                                            · linarith only [h8903, h8988, hlam]
                                                        · linarith only [h8901, h8985, hlam]
                                                      · linarith only [h8895, h8984, hlam]
                                                    · linarith only [h8839, h8983, hlam]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8838, h8902, hc02, hlam, hphi, ht0b, ht5b, p8955_1, u5ehi3]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8839, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8895, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8901, hlam, p8955_1]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8903, hlam, p8955_1]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8840, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8896, hlam, p8955_0]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h8902, hlam, p8955_1]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [h7600, h8837, h8896, h8901, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8955_1]
                                                  · have p8955_0 := h8955c.1
                                                    have p8955_1 := h8955c.2.1
                                                    have p8955_2 := h8955c.2.2.1
                                                    have p8955_3 := h8955c.2.2.2
                                                    linarith only [hlam, p8955_0]
                                                · linarith only [h8843, h8954, hlam]
                                            · linarith only [h8841, h8951, hlam]
                                          · linarith only [h8839, h8950, hlam]
                                        · linarith only [h8836, h8949, hlam]
                                      · have p8907_0 := h8907c.1
                                        have p8907_1 := h8907c.2.1
                                        have p8907_2 := h8907c.2.2.1
                                        have p8907_3 := h8907c.2.2.2
                                        linarith only [hlam, p8907_0]
                                · linarith only [h7600, h8837, h8894, h8898, h8901, h8902, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9011 | h9011
                                · linarith only [h7600, h8841, h8894, h8901, h9011, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9013 | h9013
                                  · linarith only [h8836, h8843, h8897, h8901, h9013, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9015 | h9015
                                    · linarith only [h8836, h8843, h8897, h9015, hlam]
                                    · rcases h0bigk with h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c | h9017c
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h0, hlam, p9017_1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h7600, hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h7600, h8836, h8894, h8897, h8901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9017_1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h7600, h8894, hc12, hlam, hphi, ht01, ht0b, ht5b, p9017_1, u5ehi0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h0, h8837, hc12, hlam, hphi, ht01, ht0b, ht5b, p9017_1, u5ehi1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h0, h7600, h8836, h8897, h8901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9017_1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        rcases p9017_3 (m.d 0 1) (by simp) with h9026 | h9026
                                        · linarith only [h0, h9026, hlam]
                                        · linarith only [h8836, h9026, hlam]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        rcases p9017_3 (m.d 0 1) (by simp) with h9029 | h9029
                                        · linarith only [h0, h9029, hlam]
                                        · linarith only [h8837, h9029, hlam]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8837, h8897, h8899, h8901, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9017_1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8838, hlam, p9017_1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        rcases p9017_3 (m.d 0 1) (by simp) with h9035 | h9035
                                        · linarith only [h7600, h9035, hlam]
                                        · linarith only [h8836, h9035, hlam]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        rcases p9017_3 (m.d 0 1) (by simp) with h9038 | h9038
                                        · linarith only [h7600, h9038, hlam]
                                        · linarith only [h8837, h9038, hlam]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8836, hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8839, hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8841, hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8843, hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8837, hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8840, hlam, p9017_1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h8842, hlam, p9017_0]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [h0, h8836, h8837, h8897, h8901, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9017_1]
                                      · have p9017_0 := h9017c.1
                                        have p9017_1 := h9017c.2.1
                                        have p9017_2 := h9017c.2.2.1
                                        have p9017_3 := h9017c.2.2.2
                                        linarith only [hlam, p9017_0]
                          · linarith only [h7600, h8837, h8898, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h7600, h8837, h8896, h8897, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h7600, h8837, h8894, h8896, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h7600, h8837, h8894, h8895, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h8837, h8894, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h7600, h8837, h8842, hlam]
            · linarith only [h7600, h8836, h8841, hlam]
          · linarith only [h0, h8837, h8840, hlam]
        · linarith only [h7600, h8836, h8838, h8839, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9060 | h9060
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9061 | h9061
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9062 | h9062
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9063 | h9063
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9064 | h9064
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9065 | h9065
                  · linarith only [h8838, h9061, h9065, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h8836, h9064, h9065, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9068 | h9068
                  · linarith only [h0, h8837, h8838, h9068, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                  · linarith only [h0, h8837, h9068, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h8837, h8838, h9063, hlam]
            · linarith only [h0, h8836, h8838, h9062, hlam]
          · linarith only [h0, h8837, h9061, hlam]
        · linarith only [h0, h8836, h9060, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h9075 | h9075
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9076 | h9076
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9077 | h9077
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9078 | h9078
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9079 | h9079
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9080 | h9080
                · linarith only [h8836, h8837, h9080, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9082 | h9082
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9083 | h9083
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9084 | h9084
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9085 | h9085
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9086 | h9086
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9087 | h9087
                            · linarith only [h8836, h8837, h9080, h9082, h9086, h9087, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9089 | h9089
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9090 | h9090
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9091 | h9091
                                  · linarith only [h8836, h8837, h9083, h9087, h9091, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9093 | h9093
                                    · linarith only [h8837, h9075, h9087, h9089, h9093, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                    · rcases h0bigk with h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c | h9095c
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h0, hlam, p9095_1]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h7600, hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h8837, h9087, hc04, hc45, hlam, hphi, p9095_1]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h8837, hlam, p9095_1]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        rcases p9095_3 (m.d 0 1) (by simp) with h9101 | h9101
                                        · linarith only [h0, h9101, hlam]
                                        · rcases p9095_3 (m.d 0 2) (by simp) with h9103 | h9103
                                          · rcases p9095_3 (m.d 0 3) (by simp) with h9104 | h9104
                                            · linarith only [h9075, h9104, hlam]
                                            · linarith only [h7600, h9104, hlam]
                                          · linarith only [h0, h9103, hlam]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h0, h9079, hc12, hlam, hphi, ht01, ht0b, ht5b, p9095_1, u5ehi3]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        rcases p9095_3 (m.d 0 1) (by simp) with h9110 | h9110
                                        · linarith only [h0, h9110, hlam]
                                        · linarith only [h8836, h9110, hlam]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        rcases p9095_3 (m.d 0 1) (by simp) with h9113 | h9113
                                        · linarith only [h0, h9113, hlam]
                                        · rcases p9095_3 (m.d 0 2) (by simp) with h9115 | h9115
                                          · rcases p9095_3 (m.d 0 3) (by simp) with h9116 | h9116
                                            · linarith only [h9075, h9116, hlam]
                                            · linarith only [h9079, h9116, hlam]
                                          · linarith only [h9077, h9115, hlam]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        rcases p9095_3 (m.d 0 1) (by simp) with h9120 | h9120
                                        · linarith only [h7600, h9120, hlam]
                                        · rcases p9095_3 (m.d 0 2) (by simp) with h9122 | h9122
                                          · rcases p9095_3 (m.d 0 3) (by simp) with h9123 | h9123
                                            · rcases p9095_3 (m.d 0 4) (by simp) with h9124 | h9124
                                              · linarith only [h9078, h9124, hlam]
                                              · rcases p9095_3 (m.d 0 5) (by simp) with h9126 | h9126
                                                · linarith only [h9079, h9126, hlam]
                                                · linarith only [h8837, h9126, hlam]
                                            · linarith only [h7600, h9123, hlam]
                                          · linarith only [h0, h9122, hlam]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h9075, hlam, p9095_1]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        rcases p9095_3 (m.d 0 1) (by simp) with h9133 | h9133
                                        · linarith only [h7600, h9133, hlam]
                                        · linarith only [h8836, h9133, hlam]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        rcases p9095_3 (m.d 0 1) (by simp) with h9136 | h9136
                                        · linarith only [h7600, h9136, hlam]
                                        · rcases p9095_3 (m.d 0 2) (by simp) with h9138 | h9138
                                          · rcases p9095_3 (m.d 0 3) (by simp) with h9139 | h9139
                                            · rcases p9095_3 (m.d 0 4) (by simp) with h9140 | h9140
                                              · linarith only [h9078, h9140, hlam]
                                              · rcases p9095_3 (m.d 0 5) (by simp) with h9142 | h9142
                                                · linarith only [h9079, h9142, hlam]
                                                · rcases h2bigk with h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c | h9144c
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h0, hlam, p9144_1]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h0, h9090, hc12, hlam, hphi, ht01, ht0b, ht5b, p9144_1, u5ehi3]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h8836, h8837, h9075, h9083, hlam, p9095_1, p9144_2]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    rcases p9144_3 (m.d 0 2) (by simp) with h9149 | h9149
                                                    · rcases p9144_3 (m.d 1 2) (by simp) with h9150 | h9150
                                                      · rcases p9144_3 (m.d 2 3) (by simp) with h9151 | h9151
                                                        · linarith only [h9075, h9151, hlam]
                                                        · linarith only [h9090, h9151, hlam]
                                                      · linarith only [h9084, h9150, hlam]
                                                    · linarith only [h9149, hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h8837, h9075, hc01, hc12, hlam, hphi, p9095_1, p9144_1]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9090, hc12, hlam, hphi, ht01, ht0b, ht5b, p9144_1, u5ehi3]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h0, h8836, h8837, h9075, h9083, hlam, p9095_1, p9144_2]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    rcases p9144_3 (m.d 0 2) (by simp) with h9160 | h9160
                                                    · linarith only [h0, h9160, hlam]
                                                    · linarith only [h9077, h9160, hlam]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9075, hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9082, hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    rcases p9144_3 (m.d 0 2) (by simp) with h9166 | h9166
                                                    · rcases p9144_3 (m.d 1 2) (by simp) with h9167 | h9167
                                                      · rcases p9144_3 (m.d 2 3) (by simp) with h9168 | h9168
                                                        · rcases p9144_3 (m.d 2 4) (by simp) with h9169 | h9169
                                                          · linarith only [h9089, h9169, hlam]
                                                          · rcases p9144_3 (m.d 2 5) (by simp) with h9171 | h9171
                                                            · linarith only [h9090, h9171, hlam]
                                                            · linarith only [h9091, h9171, hlam]
                                                        · linarith only [h9089, h9168, hlam]
                                                      · linarith only [h9083, h9167, hlam]
                                                    · linarith only [h9076, h9166, hlam]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9075, h9090, hc02, hlam, hphi, ht0b, ht5b, p9144_1, u5ehi3]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9076, hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9083, hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9089, hlam, p9144_1]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9091, hlam, p9144_1]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9077, hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9084, hlam, p9144_0]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9090, hlam, p9144_1]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [h9077, h9089, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9095_1, p9144_1]
                                                  · have p9144_0 := h9144c.1
                                                    have p9144_1 := h9144c.2.1
                                                    have p9144_2 := h9144c.2.2.1
                                                    have p9144_3 := h9144c.2.2.2
                                                    linarith only [hlam, p9144_0]
                                            · linarith only [h9079, h9139, hlam]
                                          · linarith only [h9077, h9138, hlam]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h8836, hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h9076, hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h9078, hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h9080, hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h8836, h8837, h9083, h9087, h9089, hc34, hc45, hlam, hphi, p9095_1]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h9077, hlam, p9095_1]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [h9079, hlam, p9095_0]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        rcases p9095_3 (m.d 0 1) (by simp) with h9198 | h9198
                                        · linarith only [h8837, h9198, hlam]
                                        · linarith only [h8836, h9198, hlam]
                                      · have p9095_0 := h9095c.1
                                        have p9095_1 := h9095c.2.1
                                        have p9095_2 := h9095c.2.2.1
                                        have p9095_3 := h9095c.2.2.2
                                        linarith only [hlam, p9095_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9202 | h9202
                                  · linarith only [h0, h8836, h8837, h9083, h9087, h9202, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9204 | h9204
                                    · linarith only [h0, h8837, h9075, h9079, h9087, h9089, h9090, h9204, hc01, hc12, hlam, hphi]
                                    · rcases h0bigk with h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c | h9206c
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h0, hlam, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h7600, hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h8836, h8837, h9083, h9087, h9089, hc34, hc45, hlam, hphi, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h8837, hlam, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        rcases p9206_3 (m.d 0 1) (by simp) with h9212 | h9212
                                        · linarith only [h0, h9212, hlam]
                                        · rcases p9206_3 (m.d 0 2) (by simp) with h9214 | h9214
                                          · rcases p9206_3 (m.d 0 3) (by simp) with h9215 | h9215
                                            · linarith only [h9075, h9215, hlam]
                                            · linarith only [h7600, h9215, hlam]
                                          · linarith only [h0, h9214, hlam]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h0, h9079, h9090, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        rcases p9206_3 (m.d 0 1) (by simp) with h9221 | h9221
                                        · linarith only [h0, h9221, hlam]
                                        · linarith only [h8836, h9221, hlam]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h0, h9079, h9089, h9090, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        rcases p9206_3 (m.d 0 1) (by simp) with h9225 | h9225
                                        · linarith only [h7600, h9225, hlam]
                                        · rcases p9206_3 (m.d 0 2) (by simp) with h9227 | h9227
                                          · rcases p9206_3 (m.d 0 3) (by simp) with h9228 | h9228
                                            · rcases p9206_3 (m.d 0 4) (by simp) with h9229 | h9229
                                              · linarith only [h9078, h9229, hlam]
                                              · rcases p9206_3 (m.d 0 5) (by simp) with h9231 | h9231
                                                · linarith only [h9079, h9231, hlam]
                                                · linarith only [h8837, h9231, hlam]
                                            · linarith only [h7600, h9228, hlam]
                                          · linarith only [h0, h9227, hlam]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h9075, hlam, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        rcases p9206_3 (m.d 0 1) (by simp) with h9238 | h9238
                                        · linarith only [h7600, h9238, hlam]
                                        · linarith only [h8836, h9238, hlam]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h9079, h9089, h9090, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h8836, hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h9076, hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h9078, hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h9080, hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h8836, h8837, h9083, h9087, h9089, hc34, hc45, hlam, hphi, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h9077, hlam, p9206_1]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [h9079, hlam, p9206_0]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        rcases p9206_3 (m.d 0 1) (by simp) with h9250 | h9250
                                        · linarith only [h8837, h9250, hlam]
                                        · linarith only [h8836, h9250, hlam]
                                      · have p9206_0 := h9206c.1
                                        have p9206_1 := h9206c.2.1
                                        have p9206_2 := h9206c.2.2.1
                                        have p9206_3 := h9206c.2.2.2
                                        linarith only [hlam, p9206_0]
                              · linarith only [h8836, h8837, h9085, h9087, h9089, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h7600, h9079, h9086, hlam]
                        · linarith only [h7600, h9078, h9085, hlam]
                      · linarith only [h0, h9075, h9077, h9079, h9084, hlam]
                    · linarith only [h0, h9076, h9083, hlam]
                  · linarith only [h0, h9075, h9082, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9260 | h9260
                · linarith only [h8836, h8837, h9260, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9262 | h9262
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9263 | h9263
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9264 | h9264
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9265 | h9265
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9266 | h9266
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9267 | h9267
                            · linarith only [h7600, h8836, h9079, h9262, h9266, h9267, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9269 | h9269
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9270 | h9270
                                · linarith only [h9075, h9079, h9270, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9272 | h9272
                                  · linarith only [h7600, h8836, h9076, h9079, h9266, h9267, h9272, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9274 | h9274
                                    · linarith only [h7600, h8836, h9079, h9263, h9266, h9267, h9269, h9274, hlam]
                                    · rcases h0bigk with h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c | h9276c
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h0, hlam, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h7600, hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h7600, h9079, h9266, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h8837, hlam, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        rcases p9276_3 (m.d 0 1) (by simp) with h9282 | h9282
                                        · linarith only [h0, h9282, hlam]
                                        · rcases p9276_3 (m.d 0 2) (by simp) with h9284 | h9284
                                          · rcases p9276_3 (m.d 0 3) (by simp) with h9285 | h9285
                                            · linarith only [h9075, h9285, hlam]
                                            · linarith only [h7600, h9285, hlam]
                                          · linarith only [h0, h9284, hlam]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        rcases p9276_3 (m.d 0 1) (by simp) with h9290 | h9290
                                        · linarith only [h0, h9290, hlam]
                                        · rcases p9276_3 (m.d 0 2) (by simp) with h9292 | h9292
                                          · rcases p9276_3 (m.d 0 3) (by simp) with h9293 | h9293
                                            · linarith only [h9075, h9293, hlam]
                                            · rcases p9276_3 (m.d 0 4) (by simp) with h9295 | h9295
                                              · linarith only [h9076, h9295, hlam]
                                              · rcases p9276_3 (m.d 0 5) (by simp) with h9297 | h9297
                                                · linarith only [h9077, h9297, hlam]
                                                · linarith only [h9079, h9297, hlam]
                                          · linarith only [h9075, h9292, hlam]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        rcases p9276_3 (m.d 0 1) (by simp) with h9301 | h9301
                                        · linarith only [h0, h9301, hlam]
                                        · linarith only [h8836, h9301, hlam]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        rcases p9276_3 (m.d 0 1) (by simp) with h9304 | h9304
                                        · linarith only [h0, h9304, hlam]
                                        · rcases p9276_3 (m.d 0 2) (by simp) with h9306 | h9306
                                          · rcases p9276_3 (m.d 0 3) (by simp) with h9307 | h9307
                                            · linarith only [h9075, h9307, hlam]
                                            · rcases p9276_3 (m.d 0 4) (by simp) with h9309 | h9309
                                              · linarith only [h9076, h9309, hlam]
                                              · rcases p9276_3 (m.d 0 5) (by simp) with h9311 | h9311
                                                · linarith only [h9077, h9311, hlam]
                                                · rcases h2bigk with h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c | h9313c
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h0, hlam, p9313_1]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    rcases p9313_3 (m.d 0 2) (by simp) with h9316 | h9316
                                                    · rcases p9313_3 (m.d 1 2) (by simp) with h9317 | h9317
                                                      · rcases p9313_3 (m.d 2 3) (by simp) with h9318 | h9318
                                                        · linarith only [h9318, hlam, p9313_0]
                                                        · rcases p9313_3 (m.d 2 4) (by simp) with h9320 | h9320
                                                          · linarith only [h9076, h9320, hlam]
                                                          · rcases p9313_3 (m.d 2 5) (by simp) with h9322 | h9322
                                                            · linarith only [h9077, h9322, hlam]
                                                            · linarith only [h9270, h9322, hlam]
                                                      · linarith only [h9262, h9317, hlam]
                                                    · linarith only [h9316, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h7600, h8836, h9079, h9263, hlam, p9276_1, p9313_2]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    rcases p9313_3 (m.d 0 2) (by simp) with h9328 | h9328
                                                    · rcases p9313_3 (m.d 1 2) (by simp) with h9329 | h9329
                                                      · rcases p9313_3 (m.d 2 3) (by simp) with h9330 | h9330
                                                        · linarith only [h9075, h9330, hlam]
                                                        · rcases p9313_3 (m.d 2 4) (by simp) with h9332 | h9332
                                                          · linarith only [h9076, h9332, hlam]
                                                          · rcases p9313_3 (m.d 2 5) (by simp) with h9334 | h9334
                                                            · linarith only [h9334, hlam, p9313_0]
                                                            · rcases h3bigk with h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c | h9336c
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h7600, hlam, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h0, h9079, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9276_1, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h0, h9079, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9276_1, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9079, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                rcases p9336_3 (m.d 0 3) (by simp) with h9342 | h9342
                                                                · linarith only [h7600, h9342, hlam]
                                                                · rcases p9336_3 (m.d 1 3) (by simp) with h9344 | h9344
                                                                  · rcases p9336_3 (m.d 2 3) (by simp) with h9345 | h9345
                                                                    · linarith only [h9262, h9345, hlam]
                                                                    · rcases p9336_3 (m.d 3 4) (by simp) with h9347 | h9347
                                                                      · linarith only [h9265, h9347, hlam]
                                                                      · rcases p9336_3 (m.d 3 5) (by simp) with h9349 | h9349
                                                                        · linarith only [h9266, h9349, hlam]
                                                                        · linarith only [h9079, h9349, hlam]
                                                                  · linarith only [h7600, h9344, hlam]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                rcases p9336_3 (m.d 0 3) (by simp) with h9354 | h9354
                                                                · linarith only [h7600, h9354, hlam]
                                                                · linarith only [h9075, h9354, hlam]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9075, h9079, h9266, h9269, hlam, p9336_2]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h7600, h9079, hc01, hc13, hlam, hphi, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9075, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9262, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9075, h9079, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9276_1, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9270, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9078, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9265, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9269, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9274, hlam, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h7600, h9262, h9266, hc01, hc12, hlam, hphi, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9266, hlam, p9336_0]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [h9266, h9267, h9269, hc34, hc45, hlam, hphi, p9336_1]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                rcases p9336_3 (m.d 0 3) (by simp) with h9372 | h9372
                                                                · linarith only [h9079, h9372, hlam]
                                                                · linarith only [h9078, h9372, hlam]
                                                              · have p9336_0 := h9336c.1
                                                                have p9336_1 := h9336c.2.1
                                                                have p9336_2 := h9336c.2.2.1
                                                                have p9336_3 := h9336c.2.2.2
                                                                linarith only [hlam, p9336_0]
                                                      · linarith only [h9264, h9329, hlam]
                                                    · linarith only [h9328, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h7600, h8836, h9079, h9263, h9269, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9276_1, p9313_1]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    rcases p9313_3 (m.d 0 2) (by simp) with h9380 | h9380
                                                    · linarith only [h0, h9380, hlam]
                                                    · linarith only [h9075, h9380, hlam]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h0, h7600, h8836, h9079, h9263, hlam, p9276_1, p9313_2]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    rcases p9313_3 (m.d 0 2) (by simp) with h9384 | h9384
                                                    · linarith only [h0, h9384, hlam]
                                                    · linarith only [h9077, h9384, hlam]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9075, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9262, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9075, h9079, h9269, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9276_1, p9313_1]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9270, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9076, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9263, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9269, hlam, p9313_1]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9272, hlam, p9313_1]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9077, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h9264, hlam, p9313_0]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h0, h9077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9276_1, p9313_1]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [h0, h9077, h9269, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9276_1, p9313_1]
                                                  · have p9313_0 := h9313c.1
                                                    have p9313_1 := h9313c.2.1
                                                    have p9313_2 := h9313c.2.2.1
                                                    have p9313_3 := h9313c.2.2.2
                                                    linarith only [hlam, p9313_0]
                                          · linarith only [h9077, h9306, hlam]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h8836, h8837, h9079, h9263, h9267, h9269, hc34, hc45, hlam, hphi, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h9075, hlam, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h9079, h9262, h9266, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h9079, hlam, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h8836, hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h9076, hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h9078, hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h9260, hlam, p9276_0]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h8836, h8837, h9263, h9267, h9269, hc34, hc45, hlam, hphi, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h9077, hlam, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [h7600, h8836, h9079, h9262, h9263, h9266, h9269, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9276_1]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        rcases p9276_3 (m.d 0 1) (by simp) with h9416 | h9416
                                        · linarith only [h8837, h9416, hlam]
                                        · linarith only [h8836, h9416, hlam]
                                      · have p9276_0 := h9276c.1
                                        have p9276_1 := h9276c.2.1
                                        have p9276_2 := h9276c.2.2.1
                                        have p9276_3 := h9276c.2.2.2
                                        linarith only [hlam, p9276_0]
                              · linarith only [h9078, h9079, h9262, h9266, h9269, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9421 | h9421
                            · linarith only [h7600, h8836, h9260, h9266, h9421, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9423 | h9423
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9424 | h9424
                                · linarith only [h7600, h8836, h9263, h9266, h9423, h9424, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9426 | h9426
                                  · linarith only [h7600, h8836, h9263, h9266, h9421, h9426, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9428 | h9428
                                    · linarith only [h7600, h8836, h9263, h9266, h9421, h9423, h9428, hlam]
                                    · linarith only [h7600, h8836, h9263, h9266, h9423, h9428, hc34, hc45, hlam, hphi]
                              · linarith only [h7600, h9078, h9266, h9423, hc23, hc35, hlam, hphi]
                        · linarith only [h7600, h8836, h9078, h9265, hlam]
                      · linarith only [h0, h9077, h9264, hlam]
                    · linarith only [h0, h9076, h9263, hlam]
                  · linarith only [h0, h9075, h9262, hlam]
            · linarith only [h7600, h8836, h9078, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9437 | h9437
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9438 | h9438
              · linarith only [h9075, h9077, h9438, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9440 | h9440
                · linarith only [h7600, h8836, h9075, h9077, h9440, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9442 | h9442
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9443 | h9443
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9444 | h9444
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9445 | h9445
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9446 | h9446
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9447 | h9447
                            · linarith only [h7600, h8836, h9075, h9077, h9440, h9444, h9447, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9449 | h9449
                              · linarith only [h9075, h9077, h9444, h9449, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h9075, h9077, h9437, h9444, h9449, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9452 | h9452
                            · linarith only [h7600, h8836, h9075, h9077, h9444, h9452, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9454 | h9454
                              · linarith only [h9075, h9077, h9444, h9454, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h9075, h9077, h9437, h9444, h9454, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h7600, h8836, h9437, h9445, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9458 | h9458
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9459 | h9459
                          · linarith only [h7600, h8836, h9438, h9442, h9443, h9444, h9459, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9461 | h9461
                            · linarith only [h0, h8836, h9444, h9461, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9463 | h9463
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9464 | h9464
                                · linarith only [h0, h9075, h9444, h9459, h9464, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9466 | h9466
                                  · linarith only [h7600, h8836, h9443, h9461, h9466, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                  · linarith only [h7600, h8836, h9442, h9444, h9466, hc14, hc45, hlam, hphi]
                              · linarith only [h7600, h9437, h9459, h9463, hc23, hc35, hlam, hphi]
                        · linarith only [h7600, h8836, h9437, h9458, hlam]
                    · linarith only [h0, h9076, h9443, hlam]
                  · linarith only [h0, h9075, h9442, hlam]
            · linarith only [h7600, h8836, h9437, hlam]
        · linarith only [h0, h8836, h9076, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h9475 | h9475
        · rcases m.htr 0 2 5 (by decide) (by decide) with h9476 | h9476
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9477 | h9477
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9478 | h9478
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9479 | h9479
                · linarith only [h8836, h8837, h9479, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9481 | h9481
                  · linarith only [h9075, h9476, h9481, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9483 | h9483
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9484 | h9484
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9485 | h9485
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9486 | h9486
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9487 | h9487
                            · linarith only [h8836, h8837, h9479, h9484, h9487, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9489 | h9489
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9490 | h9490
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9491 | h9491
                                  · linarith only [h8836, h8837, h9483, h9487, h9491, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9493 | h9493
                                    · linarith only [h8836, h8837, h9477, h9487, h9493, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c | h9495c
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h0, hlam, p9495_1]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h7600, hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h8836, h8837, h9481, h9483, h9484, h9489, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9495_1]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h8837, hlam, p9495_1]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h0, h9481, hc01, hc23, hlam, hphi, ht12, p9495_1]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h9075, hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        rcases p9495_3 (m.d 0 1) (by simp) with h9504 | h9504
                                        · linarith only [h0, h9504, hlam]
                                        · linarith only [h8836, h9504, hlam]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h0, h9481, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9495_1, u5ehi0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        rcases p9495_3 (m.d 0 1) (by simp) with h9508 | h9508
                                        · linarith only [h7600, h9508, hlam]
                                        · rcases p9495_3 (m.d 0 2) (by simp) with h9510 | h9510
                                          · linarith only [h9075, h9510, hlam]
                                          · linarith only [h0, h9510, hlam]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h7600, h9476, h9481, h9490, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9495_1, u5ehi3]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        rcases p9495_3 (m.d 0 1) (by simp) with h9515 | h9515
                                        · linarith only [h7600, h9515, hlam]
                                        · linarith only [h8836, h9515, hlam]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        rcases p9495_3 (m.d 0 1) (by simp) with h9518 | h9518
                                        · linarith only [h7600, h9518, hlam]
                                        · rcases p9495_3 (m.d 0 2) (by simp) with h9520 | h9520
                                          · linarith only [h9075, h9520, hlam]
                                          · linarith only [h9476, h9520, hlam]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h8836, hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h9475, hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h9477, hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h9479, hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h8836, h8837, h9481, h9483, h9484, h9489, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9495_1]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h9476, hlam, p9495_1]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [h9478, hlam, p9495_0]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        rcases p9495_3 (m.d 0 1) (by simp) with h9531 | h9531
                                        · linarith only [h8837, h9531, hlam]
                                        · linarith only [h8836, h9531, hlam]
                                      · have p9495_0 := h9495c.1
                                        have p9495_1 := h9495c.2.1
                                        have p9495_2 := h9495c.2.2.1
                                        have p9495_3 := h9495c.2.2.2
                                        linarith only [hlam, p9495_0]
                                · linarith only [h0, h8836, h9481, h9483, h9489, h9490, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h9481, h9489, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h7600, h9478, h9486, hlam]
                        · linarith only [h7600, h9477, h9485, hlam]
                      · linarith only [h0, h8836, h9476, h9483, h9484, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h9475, h9483, hlam]
              · linarith only [h9075, h9476, h9478, hlam]
            · linarith only [h0, h8836, h9075, h9477, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h9543 | h9543
            · rcases m.htr 0 3 5 (by decide) (by decide) with h9544 | h9544
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9545 | h9545
                · linarith only [h0, h8836, h9476, h9545, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9547 | h9547
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9548 | h9548
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9549 | h9549
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9550 | h9550
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9551 | h9551
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9552 | h9552
                            · linarith only [h0, h8836, h9075, h9545, h9547, h9552, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9554 | h9554
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9555 | h9555
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9556 | h9556
                                  · linarith only [h0, h8836, h9476, h9548, h9549, h9552, h9556, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9558 | h9558
                                    · linarith only [h0, h8836, h9476, h9548, h9549, h9552, h9554, h9558, hlam]
                                    · rcases h0bigk with h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c | h9560c
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h0, hlam, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h7600, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h0, h9476, h9547, h9555, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h8837, hlam, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h9476, h9547, h9555, hc01, hc12, hlam, hphi, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h9075, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h8836, h9476, h9547, h9548, h9554, h9555, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h9476, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h8836, h9075, h9547, h9548, h9554, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h0, h8836, h9075, h9547, h9548, h9554, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        rcases p9560_3 (m.d 0 1) (by simp) with h9574 | h9574
                                        · linarith only [h7600, h9574, hlam]
                                        · linarith only [h8836, h9574, hlam]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h0, h8836, h9075, h9476, h9547, h9548, h9554, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h8836, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h9475, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h9543, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h9545, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h8836, h8837, h9548, h9552, h9554, hc34, hc45, hlam, hphi, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h0, h8836, h9476, h9547, h9548, h9554, h9555, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9560_1]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [h9544, hlam, p9560_0]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        rcases p9560_3 (m.d 0 1) (by simp) with h9586 | h9586
                                        · linarith only [h8837, h9586, hlam]
                                        · linarith only [h8836, h9586, hlam]
                                      · have p9560_0 := h9560c.1
                                        have p9560_1 := h9560c.2.1
                                        have p9560_2 := h9560c.2.2.1
                                        have p9560_3 := h9560c.2.2.2
                                        linarith only [hlam, p9560_0]
                                · linarith only [h9075, h9544, h9555, hlam]
                              · linarith only [h9075, h9543, h9554, hlam]
                          · linarith only [h7600, h9544, h9551, hlam]
                        · linarith only [h9075, h9543, h9547, h9550, hlam]
                      · linarith only [h9075, h9547, h9549, hc02, hc25, hlam, hphi]
                    · linarith only [h0, h8836, h9075, h9547, h9548, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9596 | h9596
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9597 | h9597
                      · linarith only [h0, h8836, h9476, h9547, h9596, h9597, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9599 | h9599
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9600 | h9600
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9601 | h9601
                            · linarith only [h0, h8836, h9547, h9601, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9603 | h9603
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9604 | h9604
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9605 | h9605
                                  · linarith only [h0, h8836, h9596, h9597, h9601, h9604, h9605, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                                  · linarith only [h0, h8836, h9596, h9597, h9603, h9605, hc34, hc45, hlam, hphi]
                                · linarith only [h7600, h9544, h9547, h9604, hlam]
                              · linarith only [h0, h8836, h9547, h9596, h9603, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h7600, h9544, h9600, hlam]
                        · linarith only [h7600, h9543, h9599, hlam]
                    · linarith only [h0, h8836, h9475, h9596, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h9613 | h9613
                · linarith only [h0, h8836, h9075, h9544, h9613, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h9615 | h9615
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9616 | h9616
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9617 | h9617
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9618 | h9618
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9619 | h9619
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9620 | h9620
                            · linarith only [h0, h8836, h9075, h9544, h9613, h9615, h9619, h9620, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9622 | h9622
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9623 | h9623
                                · linarith only [h0, h9075, h9544, h9615, h9623, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h8836, h9075, h9615, h9616, h9619, h9622, h9623, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h8836, h9075, h9543, h9616, h9622, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9627 | h9627
                            · linarith only [h0, h8836, h9075, h9627, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9629 | h9629
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9630 | h9630
                                · linarith only [h7600, h8836, h9616, h9619, h9629, h9630, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9632 | h9632
                                  · linarith only [h0, h8836, h9075, h9615, h9616, h9627, h9632, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9634 | h9634
                                    · linarith only [h0, h8836, h9075, h9615, h9616, h9619, h9627, h9629, h9634, hlam]
                                    · linarith only [h0, h8836, h9075, h9615, h9616, h9619, h9629, h9634, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h8836, h9075, h9543, h9616, h9629, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h8836, h9075, h9543, h9615, h9618, hlam]
                      · linarith only [h0, h8836, h9075, h9615, h9616, h9617, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h8836, h9075, h9615, h9616, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9641 | h9641
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h9642 | h9642
                      · linarith only [h0, h8836, h9476, h9615, h9641, h9642, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h9644 | h9644
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h9645 | h9645
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9646 | h9646
                            · linarith only [h0, h8836, h9615, h9646, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9648 | h9648
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9649 | h9649
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h9650 | h9650
                                  · linarith only [h0, h8836, h9075, h9544, h9615, h9641, h9645, h9646, h9650, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                                  · linarith only [h0, h8836, h9641, h9642, h9648, h9650, hc34, hc45, hlam, hphi]
                                · linarith only [h9615, h9645, h9649, hlam]
                              · linarith only [h0, h8836, h9075, h9544, h9615, h9641, h9645, h9648, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h9655 | h9655
                            · linarith only [h0, h8836, h9615, h9645, h9655, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h9657 | h9657
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h9658 | h9658
                                · linarith only [h0, h8836, h9615, h9641, h9645, h9657, h9658, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h8836, h9615, h9641, h9657, h9658, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h8836, h9615, h9641, h9657, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h8836, h9543, h9615, h9641, h9644, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h9475, h9641, hlam]
            · linarith only [h7600, h8836, h9543, hlam]
        · linarith only [h0, h8836, h9475, hlam]
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s12 m hb0 hb2 hb3 hb5 h0 h7600 h8836

end R2N4
