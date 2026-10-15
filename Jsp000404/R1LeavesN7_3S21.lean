import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S20

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7278000 in
set_option maxHeartbeats 7278000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h9870 | h9870
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9871 | h9871
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9872 | h9872
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9873 | h9873
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9874 | h9874
          · linarith only [h0, h4, h9874, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9876 | h9876
            · linarith only [h0, h8674, h9876, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9878 | h9878
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9879 | h9879
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9880 | h9880
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9881 | h9881
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h9882 | h9882
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h9883 | h9883
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h9884 | h9884
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h9885 | h9885
                            · rcases h1bigk with h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c | h9886c
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                rcases p9886_3 (m.d 0 1) (by simp) with h9888 | h9888
                                · rcases p9886_3 (m.d 1 2) (by simp) with h9889 | h9889
                                  · linarith only [h9889, hlam, p9886_0]
                                  · rcases p9886_3 (m.d 1 3) (by simp) with h9891 | h9891
                                    · linarith only [h1, h9891, hlam]
                                    · linarith only [h9874, h9891, hlam]
                                · linarith only [h9888, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h9879, h9885, hc01, hc45, hlam, hphi, ht0b, ht5b, p9886_1]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                rcases p9886_3 (m.d 0 1) (by simp) with h9896 | h9896
                                · rcases p9886_3 (m.d 1 2) (by simp) with h9897 | h9897
                                  · linarith only [h0, h9897, hlam]
                                  · rcases p9886_3 (m.d 1 3) (by simp) with h9899 | h9899
                                    · linarith only [h1, h9899, hlam]
                                    · linarith only [h9879, h9899, hlam]
                                · linarith only [h9896, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                rcases p9886_3 (m.d 0 1) (by simp) with h9903 | h9903
                                · rcases p9886_3 (m.d 1 2) (by simp) with h9904 | h9904
                                  · linarith only [h0, h9904, hlam]
                                  · linarith only [h9878, h9904, hlam]
                                · linarith only [h9903, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h0, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h9874, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h9876, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                rcases p9886_3 (m.d 0 1) (by simp) with h9912 | h9912
                                · rcases p9886_3 (m.d 1 2) (by simp) with h9913 | h9913
                                  · rcases p9886_3 (m.d 1 3) (by simp) with h9914 | h9914
                                    · rcases p9886_3 (m.d 1 4) (by simp) with h9915 | h9915
                                      · rcases p9886_3 (m.d 1 5) (by simp) with h9916 | h9916
                                        · linarith only [h9878, h9916, hlam]
                                        · rcases h3bigk with h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c | h9918c
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9876, h9878, h9879, h9883, h9885, hc03, hc45, hlam, hphi, ht0b, ht5b, p9886_1, p9918_1]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h4, hlam, p9918_1]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            rcases p9918_3 (m.d 0 3) (by simp) with h9922 | h9922
                                            · rcases p9918_3 (m.d 1 3) (by simp) with h9923 | h9923
                                              · linarith only [h1, h9923, hlam]
                                              · linarith only [h9879, h9923, hlam]
                                            · linarith only [h9922, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            rcases p9918_3 (m.d 0 3) (by simp) with h9927 | h9927
                                            · rcases p9918_3 (m.d 1 3) (by simp) with h9928 | h9928
                                              · linarith only [h1, h9928, hlam]
                                              · linarith only [h9880, h9928, hlam]
                                            · linarith only [h9927, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h1, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9874, hlam, p9918_1]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h1, h9885, hc01, hc45, hlam, hphi, ht0b, ht5b, p9918_1]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            rcases p9918_3 (m.d 0 3) (by simp) with h9936 | h9936
                                            · rcases p9918_3 (m.d 1 3) (by simp) with h9937 | h9937
                                              · rcases p9918_3 (m.d 2 3) (by simp) with h9938 | h9938
                                                · rcases p9918_3 (m.d 3 4) (by simp) with h9939 | h9939
                                                  · linarith only [h9879, h9939, hlam]
                                                  · linarith only [h9885, h9939, hlam]
                                                · linarith only [h9883, h9938, hlam]
                                              · linarith only [h9937, hlam, p9918_0]
                                            · linarith only [h9872, h9936, hlam]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h0, h4, h9878, h9883, h9885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9886_1, p9918_1]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9874, h9878, h9883, h9885, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9886_1, p9918_1]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            rcases p9918_3 (m.d 0 3) (by simp) with h9948 | h9948
                                            · linarith only [h4, h9948, hlam]
                                            · linarith only [h9871, h9948, hlam]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h0, h4, h9878, h9883, hlam, p9886_1, p9918_2]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9871, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9879, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9882, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h1, h9879, h9885, hc01, hc45, hlam, hphi, ht0b, ht5b, p9918_1]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9872, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9880, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9883, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [h9885, hlam, p9918_0]
                                          · have p9918_0 := h9918c.1
                                            have p9918_1 := h9918c.2.1
                                            have p9918_2 := h9918c.2.2.1
                                            have p9918_3 := h9918c.2.2.2
                                            linarith only [hlam, p9918_0]
                                      · linarith only [h9881, h9915, hlam]
                                    · linarith only [h9880, h9914, hlam]
                                  · linarith only [h9878, h9913, hlam]
                                · linarith only [h3, h9912, hlam]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h1, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h1, h9878, h9883, h9885, hc01, hc45, hlam, hphi, ht0b, ht5b, p9886_1]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h1, h9876, h9878, h9883, h9885, hc01, hc45, hlam, hphi, ht0b, ht5b, p9886_1]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                rcases p9886_3 (m.d 0 1) (by simp) with h9970 | h9970
                                · rcases p9886_3 (m.d 1 2) (by simp) with h9971 | h9971
                                  · linarith only [h9874, h9971, hlam]
                                  · linarith only [h9878, h9971, hlam]
                                · linarith only [h3, h9970, hlam]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h2, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h2, h9878, h9883, h9885, hc01, hc45, hlam, hphi, ht0b, ht5b, p9886_1]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h9879, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                rcases p9886_3 (m.d 0 1) (by simp) with h9979 | h9979
                                · rcases p9886_3 (m.d 1 2) (by simp) with h9980 | h9980
                                  · linarith only [h9876, h9980, hlam]
                                  · linarith only [h9878, h9980, hlam]
                                · linarith only [h3, h9979, hlam]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h3, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h9878, hlam, p9886_1]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h9880, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [h9881, hlam, p9886_0]
                              · have p9886_0 := h9886c.1
                                have p9886_1 := h9886c.2.1
                                have p9886_2 := h9886c.2.2.1
                                have p9886_3 := h9886c.2.2.2
                                linarith only [hlam, p9886_0]
                            · rcases h1bigk with h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c | h9989c
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9878, h9884, h9885, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9876, h9878, h9879, h9884, h9885, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9876, h9878, h9884, h9885, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                rcases p9989_3 (m.d 0 1) (by simp) with h9994 | h9994
                                · rcases p9989_3 (m.d 1 2) (by simp) with h9995 | h9995
                                  · linarith only [h0, h9995, hlam]
                                  · linarith only [h9878, h9995, hlam]
                                · linarith only [h9994, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h0, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9874, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9876, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h0, h8674, h9878, h9882, h9884, h9885, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h1, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h1, h9878, h9884, h9885, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h1, h9876, h9878, h9884, h9885, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h1, h9878, h9884, h9885, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h2, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9878, h9884, h9885, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9879, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h1, h9878, h9879, h9884, h9885, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h3, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9878, hlam, p9989_1]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9880, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [h9881, hlam, p9989_0]
                              · have p9989_0 := h9989c.1
                                have p9989_1 := h9989c.2.1
                                have p9989_2 := h9989c.2.2.1
                                have p9989_3 := h9989c.2.2.2
                                linarith only [hlam, p9989_0]
                          · linarith only [h8674, h9873, h9884, hlam]
                        · linarith only [h4, h9872, h9883, hlam]
                      · linarith only [h0, h4, h9871, h9878, h9882, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h9876, h9878, h9881, hlam]
                  · linarith only [h9876, h9878, h9879, h9880, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10024 | h10024
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10025 | h10025
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10026 | h10026
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10027 | h10027
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10028 | h10028
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10029 | h10029
                            · rcases h1bigk with h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c | h10030c
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                rcases p10030_3 (m.d 0 1) (by simp) with h10032 | h10032
                                · rcases p10030_3 (m.d 1 2) (by simp) with h10033 | h10033
                                  · linarith only [h10033, hlam, p10030_0]
                                  · rcases p10030_3 (m.d 1 3) (by simp) with h10035 | h10035
                                    · linarith only [h1, h10035, hlam]
                                    · linarith only [h10035, h9874, hlam]
                                · linarith only [h10032, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                rcases p10030_3 (m.d 0 1) (by simp) with h10039 | h10039
                                · rcases p10030_3 (m.d 1 2) (by simp) with h10040 | h10040
                                  · linarith only [h0, h10040, hlam]
                                  · rcases p10030_3 (m.d 1 3) (by simp) with h10042 | h10042
                                    · linarith only [h10042, hlam, p10030_0]
                                    · rcases p10030_3 (m.d 1 4) (by simp) with h10044 | h10044
                                      · linarith only [h10044, h2, hlam]
                                      · linarith only [h10044, h9879, hlam]
                                · linarith only [h10039, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                rcases p10030_3 (m.d 0 1) (by simp) with h10048 | h10048
                                · rcases p10030_3 (m.d 1 2) (by simp) with h10049 | h10049
                                  · linarith only [h0, h10049, hlam]
                                  · rcases p10030_3 (m.d 1 3) (by simp) with h10051 | h10051
                                    · linarith only [h1, h10051, hlam]
                                    · rcases p10030_3 (m.d 1 4) (by simp) with h10053 | h10053
                                      · linarith only [h10053, hlam, p10030_0]
                                      · rcases p10030_3 (m.d 1 5) (by simp) with h10055 | h10055
                                        · linarith only [h10055, h3, hlam]
                                        · rcases h3bigk with h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c | h10057c
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            rcases p10057_3 (m.d 0 3) (by simp) with h10059 | h10059
                                            · rcases p10057_3 (m.d 1 3) (by simp) with h10060 | h10060
                                              · linarith only [h1, h10060, hlam]
                                              · rcases p10057_3 (m.d 2 3) (by simp) with h10062 | h10062
                                                · rcases p10057_3 (m.d 3 4) (by simp) with h10063 | h10063
                                                  · linarith only [h10063, h9871, hlam]
                                                  · linarith only [h10063, h9879, hlam]
                                                · linarith only [h10062, h9874, hlam]
                                            · linarith only [h1, h10059, hlam]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h4, hlam, p10057_1]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h4, h9874, h9879, hc12, hc23, hlam, hphi, p10057_1]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10027, h9871, h9874, h9878, h9879, hlam, p10057_2]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h1, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h9874, hlam, p10057_1]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h9879, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10029, h9871, h9879, hc03, hc45, hlam, hphi, ht0b, ht5b, p10057_1]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h9871, h9879, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10057_1]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            rcases p10057_3 (m.d 0 3) (by simp) with h10077 | h10077
                                            · linarith only [h10077, h4, hlam]
                                            · linarith only [h1, h10077, hlam]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10027, h10029, h9874, h9878, h9879, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10057_1]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10027, h4, h9871, h9874, h9878, h9879, hlam, p10057_2]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h9871, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10027, h10029, h9871, h9874, h9878, hc03, hc45, hlam, hphi, ht0b, ht5b, p10057_1]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10026, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            rcases p10057_3 (m.d 0 3) (by simp) with h10087 | h10087
                                            · rcases p10057_3 (m.d 1 3) (by simp) with h10088 | h10088
                                              · linarith only [h10088, h9879, hlam]
                                              · linarith only [h10024, h10088, hlam]
                                            · linarith only [h10087, h9872, hlam]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h9872, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10024, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10027, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [h10029, hlam, p10057_0]
                                          · have p10057_0 := h10057c.1
                                            have p10057_1 := h10057c.2.1
                                            have p10057_2 := h10057c.2.2.1
                                            have p10057_3 := h10057c.2.2.2
                                            linarith only [hlam, p10057_0]
                                · linarith only [h10048, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                rcases p10030_3 (m.d 0 1) (by simp) with h10098 | h10098
                                · rcases p10030_3 (m.d 1 2) (by simp) with h10099 | h10099
                                  · linarith only [h0, h10099, hlam]
                                  · linarith only [h10099, h9878, hlam]
                                · linarith only [h10098, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h0, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h9874, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h9876, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h10027, h10029, h4, h9871, h9874, h9878, h9879, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10030_1]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h1, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h1, h10027, h10029, h9878, hc01, hc45, hlam, hphi, ht0b, ht5b, p10030_1]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h9879, hlam, p10030_1]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h10027, h10029, h4, h9871, h9878, h9879, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10030_1]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h2, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h10027, h10029, h2, h9878, hc01, hc45, hlam, hphi, ht0b, ht5b, p10030_1]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h10027, h10029, h4, h9871, h9874, h9878, h9879, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10030_1]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                rcases p10030_3 (m.d 0 1) (by simp) with h10117 | h10117
                                · rcases p10030_3 (m.d 1 2) (by simp) with h10118 | h10118
                                  · linarith only [h10118, h9876, hlam]
                                  · linarith only [h10118, h9878, hlam]
                                · linarith only [h10117, h3, hlam]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h3, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h9878, hlam, p10030_1]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h10024, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [h10025, hlam, p10030_0]
                              · have p10030_0 := h10030c.1
                                have p10030_1 := h10030c.2.1
                                have p10030_2 := h10030c.2.2.1
                                have p10030_3 := h10030c.2.2.2
                                linarith only [hlam, p10030_0]
                            · linarith only [h10027, h10029, h9873, h9874, h9878, h9879, hc04, hc35, hlam, hphi, ht0b, ht5b]
                          · linarith only [h10028, h8674, h9873, hlam]
                        · linarith only [h10027, h4, h9871, h9874, h9879, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h10026, h4, h9871, hlam]
                    · linarith only [h10025, h9874, h9878, h9879, hlam]
                  · linarith only [h10024, h9874, h9878, hlam]
              · linarith only [h8674, h9870, h9878, hc12, hc24, hlam, hphi]
        · linarith only [h8674, h9870, h9873, hlam]
      · linarith only [h8674, h9870, h9871, h9872, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10136 | h10136
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10137 | h10137
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10138 | h10138
          · linarith only [h0, h10138, h4, h9870, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10140 | h10140
            · linarith only [h0, h10140, h8674, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10142 | h10142
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10143 | h10143
                · linarith only [h1, h10143, h9871, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10145 | h10145
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10146 | h10146
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10147 | h10147
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10148 | h10148
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10149 | h10149
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10150 | h10150
                            · rcases h1bigk with h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c | h10151c
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                rcases p10151_3 (m.d 0 1) (by simp) with h10153 | h10153
                                · rcases p10151_3 (m.d 1 2) (by simp) with h10154 | h10154
                                  · linarith only [h10154, hlam, p10151_0]
                                  · rcases p10151_3 (m.d 1 3) (by simp) with h10156 | h10156
                                    · linarith only [h1, h10156, hlam]
                                    · linarith only [h10138, h10156, hlam]
                                · linarith only [h10153, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                rcases p10151_3 (m.d 0 1) (by simp) with h10160 | h10160
                                · rcases p10151_3 (m.d 1 2) (by simp) with h10161 | h10161
                                  · linarith only [h0, h10161, hlam]
                                  · rcases p10151_3 (m.d 1 3) (by simp) with h10163 | h10163
                                    · linarith only [h10163, hlam, p10151_0]
                                    · rcases p10151_3 (m.d 1 4) (by simp) with h10165 | h10165
                                      · linarith only [h10165, h2, hlam]
                                      · linarith only [h10143, h10165, hlam]
                                · linarith only [h10160, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                rcases p10151_3 (m.d 0 1) (by simp) with h10169 | h10169
                                · rcases p10151_3 (m.d 1 2) (by simp) with h10170 | h10170
                                  · linarith only [h0, h10170, hlam]
                                  · rcases p10151_3 (m.d 1 3) (by simp) with h10172 | h10172
                                    · linarith only [h1, h10172, hlam]
                                    · rcases p10151_3 (m.d 1 4) (by simp) with h10174 | h10174
                                      · linarith only [h10174, hlam, p10151_0]
                                      · rcases p10151_3 (m.d 1 5) (by simp) with h10176 | h10176
                                        · linarith only [h10176, h3, hlam]
                                        · rcases h3bigk with h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c | h10178c
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10138, h10142, h10147, h10148, h10150, h9871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h4, hlam, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h9871, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10147, h10150, h9871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h1, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10138, hlam, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10143, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h1, h10147, h10150, h9871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            rcases p10178_3 (m.d 0 3) (by simp) with h10189 | h10189
                                            · linarith only [h10189, h4, hlam]
                                            · rcases p10178_3 (m.d 1 3) (by simp) with h10191 | h10191
                                              · linarith only [h10138, h10191, hlam]
                                              · rcases p10178_3 (m.d 2 3) (by simp) with h10193 | h10193
                                                · rcases p10178_3 (m.d 3 4) (by simp) with h10194 | h10194
                                                  · linarith only [h10147, h10194, hlam]
                                                  · linarith only [h10194, h9871, hlam]
                                                · linarith only [h10193, h4, hlam]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            rcases p10178_3 (m.d 0 3) (by simp) with h10198 | h10198
                                            · linarith only [h10198, h4, hlam]
                                            · linarith only [h1, h10198, hlam]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h0, h10142, h10148, h10150, h4, h9871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h0, h10142, h10147, h10148, h4, h9871, hlam, p10178_2]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h0, h10142, h10147, h10148, h10150, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10138, h10142, h10147, h10148, h10150, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10178_1]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10147, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            rcases p10178_3 (m.d 0 3) (by simp) with h10208 | h10208
                                            · linarith only [h10208, h9871, hlam]
                                            · linarith only [h10136, h10208, hlam]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10136, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10145, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10148, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [h10150, hlam, p10178_0]
                                          · have p10178_0 := h10178c.1
                                            have p10178_1 := h10178c.2.1
                                            have p10178_2 := h10178c.2.2.1
                                            have p10178_3 := h10178c.2.2.2
                                            linarith only [hlam, p10178_0]
                                · linarith only [h10169, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                rcases p10151_3 (m.d 0 1) (by simp) with h10217 | h10217
                                · rcases p10151_3 (m.d 1 2) (by simp) with h10218 | h10218
                                  · linarith only [h0, h10218, hlam]
                                  · linarith only [h10142, h10218, hlam]
                                · linarith only [h10217, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h0, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10138, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10140, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h0, h10142, h10147, h10148, h10150, h4, h9871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10151_1]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h1, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h1, h10147, h9871, hc12, hc23, hlam, hphi, p10151_1]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10143, hlam, p10151_1]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h1, h10142, h10147, h10148, h10150, h9871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10151_1]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h2, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10142, h10148, h10150, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p10151_1]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10138, h10142, h10147, h10148, h10150, h2, h9871, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10151_1]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                rcases p10151_3 (m.d 0 1) (by simp) with h10236 | h10236
                                · rcases p10151_3 (m.d 1 2) (by simp) with h10237 | h10237
                                  · linarith only [h10140, h10237, hlam]
                                  · linarith only [h10142, h10237, hlam]
                                · linarith only [h10236, h3, hlam]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h3, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10142, hlam, p10151_1]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10145, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [h10146, hlam, p10151_0]
                              · have p10151_0 := h10151c.1
                                have p10151_1 := h10151c.2.1
                                have p10151_2 := h10151c.2.2.1
                                have p10151_3 := h10151c.2.2.2
                                linarith only [hlam, p10151_0]
                            · linarith only [h10137, h10150, h9871, hlam]
                          · linarith only [h1, h10138, h10142, h10146, h10147, h10149, h3, h9871, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10136, h10148, h9871, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10249 | h10249
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10250 | h10250
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10251 | h10251
                            · rcases h1bigk with h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                rcases p10252_3 (m.d 0 1) (by simp) with h10254 | h10254
                                · rcases p10252_3 (m.d 1 2) (by simp) with h10255 | h10255
                                  · linarith only [h10255, hlam, p10252_0]
                                  · rcases p10252_3 (m.d 1 3) (by simp) with h10257 | h10257
                                    · linarith only [h1, h10257, hlam]
                                    · linarith only [h10138, h10257, hlam]
                                · linarith only [h10254, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                rcases p10252_3 (m.d 0 1) (by simp) with h10261 | h10261
                                · rcases p10252_3 (m.d 1 2) (by simp) with h10262 | h10262
                                  · linarith only [h0, h10262, hlam]
                                  · rcases p10252_3 (m.d 1 3) (by simp) with h10264 | h10264
                                    · linarith only [h10264, hlam, p10252_0]
                                    · rcases p10252_3 (m.d 1 4) (by simp) with h10266 | h10266
                                      · linarith only [h10266, h2, hlam]
                                      · linarith only [h10143, h10266, hlam]
                                · linarith only [h10261, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                rcases p10252_3 (m.d 0 1) (by simp) with h10270 | h10270
                                · rcases p10252_3 (m.d 1 2) (by simp) with h10271 | h10271
                                  · linarith only [h0, h10271, hlam]
                                  · rcases p10252_3 (m.d 1 3) (by simp) with h10273 | h10273
                                    · linarith only [h1, h10273, hlam]
                                    · rcases p10252_3 (m.d 1 4) (by simp) with h10275 | h10275
                                      · linarith only [h10275, hlam, p10252_0]
                                      · rcases p10252_3 (m.d 1 5) (by simp) with h10277 | h10277
                                        · linarith only [h10277, h3, hlam]
                                        · rcases h3bigk with h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c | h10279c
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10138, h10147, h4, hc12, hc34, hlam, hphi, ht23, p10279_1]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h4, hlam, p10279_1]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h9871, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            rcases p10279_3 (m.d 0 3) (by simp) with h10284 | h10284
                                            · rcases p10279_3 (m.d 1 3) (by simp) with h10285 | h10285
                                              · linarith only [h1, h10285, hlam]
                                              · linarith only [h10145, h10285, hlam]
                                            · linarith only [h10284, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h1, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10138, hlam, p10279_1]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10143, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10143, h10251, hc01, hc45, hlam, hphi, ht0b, ht5b, p10252_1, p10279_1]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10147, hc03, hc34, hlam, hphi, p10279_1]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10147, hc13, hc34, hlam, hphi, p10279_1]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10147, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            rcases p10279_3 (m.d 0 3) (by simp) with h10298 | h10298
                                            · linarith only [h10298, h4, hlam]
                                            · linarith only [h10136, h10298, hlam]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            rcases p10279_3 (m.d 0 3) (by simp) with h10301 | h10301
                                            · linarith only [h10301, hlam, p10279_0]
                                            · rcases p10279_3 (m.d 1 3) (by simp) with h10303 | h10303
                                              · linarith only [h10143, h10303, hlam]
                                              · rcases p10279_3 (m.d 2 3) (by simp) with h10305 | h10305
                                                · linarith only [h10147, h10305, hlam]
                                                · linarith only [h10305, h4, hlam]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            rcases p10279_3 (m.d 0 3) (by simp) with h10308 | h10308
                                            · linarith only [h10308, h9871, hlam]
                                            · linarith only [h1, h10308, hlam]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h4, hc02, hc34, hlam, hphi, ht23, p10279_1]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h0, h10142, h10147, h10249, h4, hlam, p10279_2]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10136, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10145, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10249, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [h10251, hlam, p10279_0]
                                          · have p10279_0 := h10279c.1
                                            have p10279_1 := h10279c.2.1
                                            have p10279_2 := h10279c.2.2.1
                                            have p10279_3 := h10279c.2.2.2
                                            linarith only [hlam, p10279_0]
                                · linarith only [h10270, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                rcases p10252_3 (m.d 0 1) (by simp) with h10320 | h10320
                                · rcases p10252_3 (m.d 1 2) (by simp) with h10321 | h10321
                                  · linarith only [h0, h10321, hlam]
                                  · linarith only [h10142, h10321, hlam]
                                · linarith only [h10320, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h0, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10138, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10140, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h0, h10147, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h1, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h1, h10147, h4, hc12, hc34, hlam, hphi, ht23, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10143, hlam, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                rcases p10252_3 (m.d 0 1) (by simp) with h10334 | h10334
                                · rcases p10252_3 (m.d 1 2) (by simp) with h10335 | h10335
                                  · linarith only [h10138, h10335, hlam]
                                  · linarith only [h10142, h10335, hlam]
                                · linarith only [h10334, h3, hlam]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h2, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10142, h10249, h10251, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10138, h10142, h10249, h10251, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                rcases p10252_3 (m.d 0 1) (by simp) with h10343 | h10343
                                · rcases p10252_3 (m.d 1 2) (by simp) with h10344 | h10344
                                  · linarith only [h10140, h10344, hlam]
                                  · linarith only [h10142, h10344, hlam]
                                · linarith only [h10343, h3, hlam]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h3, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10142, hlam, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10145, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10146, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                            · linarith only [h10147, h10251, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h10137, h10250, h8674, hlam]
                        · linarith only [h10136, h10249, h4, hlam]
                    · linarith only [h10140, h10142, h10146, hlam]
                  · linarith only [h10136, h10138, h10142, h10145, h9871, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · linarith only [h10142, h4, h9870, h9871, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h10137, h4, h9870, h9871, hlam]
      · linarith only [h10136, h4, h9870, hlam]
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h8674 h9870

end R2N4
