import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3336 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h3337 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h3338 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 1 2 3 (by decide) (by decide) with h3842 | h3842
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3843 | h3843
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3844 | h3844
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3845 | h3845
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3846 | h3846
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3847 | h3847
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3848 | h3848
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3849 | h3849
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3850 | h3850
                  · linarith only [h3334, h3338, h3850, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3852 | h3852
                    · linarith only [h3333, h3338, h3848, h3852, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0bigk with h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c | h3854c
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h0, hlam, p3854_1]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h2914, hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3104, hlam, p3854_1]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3265, hlam, p3854_1]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        rcases p3854_3 (m.d 0 1) (by simp) with h3860 | h3860
                        · linarith only [h0, h3860, hlam]
                        · rcases p3854_3 (m.d 0 2) (by simp) with h3862 | h3862
                          · rcases p3854_3 (m.d 0 3) (by simp) with h3863 | h3863
                            · linarith only [h3333, h3863, hlam]
                            · linarith only [h2914, h3863, hlam]
                          · linarith only [h0, h3862, hlam]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h0, h3333, h3849, hc12, hlam, hphi, ht01, ht0b, ht5b, p3854_1, u5ehi3]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        rcases p3854_3 (m.d 0 1) (by simp) with h3869 | h3869
                        · linarith only [h0, h3869, hlam]
                        · rcases p3854_3 (m.d 0 2) (by simp) with h3871 | h3871
                          · rcases p3854_3 (m.d 0 3) (by simp) with h3872 | h3872
                            · linarith only [h3333, h3872, hlam]
                            · linarith only [h3336, h3872, hlam]
                          · linarith only [h3334, h3871, hlam]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        rcases p3854_3 (m.d 0 1) (by simp) with h3876 | h3876
                        · linarith only [h0, h3876, hlam]
                        · rcases p3854_3 (m.d 0 2) (by simp) with h3878 | h3878
                          · rcases p3854_3 (m.d 0 3) (by simp) with h3879 | h3879
                            · linarith only [h3333, h3879, hlam]
                            · linarith only [h3337, h3879, hlam]
                          · linarith only [h3335, h3878, hlam]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        rcases p3854_3 (m.d 0 1) (by simp) with h3883 | h3883
                        · linarith only [h2914, h3883, hlam]
                        · rcases p3854_3 (m.d 0 2) (by simp) with h3885 | h3885
                          · rcases p3854_3 (m.d 0 3) (by simp) with h3886 | h3886
                            · rcases p3854_3 (m.d 0 4) (by simp) with h3887 | h3887
                              · linarith only [h3336, h3887, hlam]
                              · linarith only [h3104, h3887, hlam]
                            · linarith only [h2914, h3886, hlam]
                          · linarith only [h0, h3885, hlam]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3333, hlam, p3854_1]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        rcases p3854_3 (m.d 0 1) (by simp) with h3894 | h3894
                        · linarith only [h2914, h3894, hlam]
                        · rcases p3854_3 (m.d 0 2) (by simp) with h3896 | h3896
                          · rcases p3854_3 (m.d 0 3) (by simp) with h3897 | h3897
                            · rcases p3854_3 (m.d 0 4) (by simp) with h3898 | h3898
                              · linarith only [h3336, h3898, hlam]
                              · rcases p3854_3 (m.d 0 5) (by simp) with h3900 | h3900
                                · linarith only [h3337, h3900, hlam]
                                · linarith only [h3338, h3900, hlam]
                            · linarith only [h3336, h3897, hlam]
                          · linarith only [h3334, h3896, hlam]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        rcases p3854_3 (m.d 0 1) (by simp) with h3905 | h3905
                        · linarith only [h2914, h3905, hlam]
                        · rcases p3854_3 (m.d 0 2) (by simp) with h3907 | h3907
                          · rcases p3854_3 (m.d 0 3) (by simp) with h3908 | h3908
                            · rcases p3854_3 (m.d 0 4) (by simp) with h3909 | h3909
                              · linarith only [h3336, h3909, hlam]
                              · rcases p3854_3 (m.d 0 5) (by simp) with h3911 | h3911
                                · linarith only [h3337, h3911, hlam]
                                · rcases h0emin with h3913 | h3913 | h3913 | h3913 | h3913
                                  · linarith only [h0, h3913, hc12, hlam, ht01]
                                  · rcases h2bigk with h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h0, hlam, p3915_1]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h0, h3849, h3852, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3915_1, u3ehi3]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      rcases p3915_3 (m.d 0 2) (by simp) with h3919 | h3919
                                      · rcases p3915_3 (m.d 1 2) (by simp) with h3920 | h3920
                                        · rcases p3915_3 (m.d 2 3) (by simp) with h3921 | h3921
                                          · linarith only [h3333, h3921, hlam]
                                          · linarith only [h3848, h3921, hlam]
                                        · linarith only [h3843, h3920, hlam]
                                      · linarith only [h3919, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      rcases p3915_3 (m.d 0 2) (by simp) with h3926 | h3926
                                      · rcases p3915_3 (m.d 1 2) (by simp) with h3927 | h3927
                                        · rcases p3915_3 (m.d 2 3) (by simp) with h3928 | h3928
                                          · linarith only [h3333, h3928, hlam]
                                          · linarith only [h3849, h3928, hlam]
                                        · linarith only [h3844, h3927, hlam]
                                      · linarith only [h3926, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3913, hc12, hlam, ht01, p3915_1]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3849, h3852, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3915_1, u3ehi3]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      rcases p3915_3 (m.d 0 2) (by simp) with h3936 | h3936
                                      · linarith only [h0, h3936, hlam]
                                      · linarith only [h3334, h3936, hlam]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      rcases p3915_3 (m.d 0 2) (by simp) with h3939 | h3939
                                      · linarith only [h0, h3939, hlam]
                                      · linarith only [h3335, h3939, hlam]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3333, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3842, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3333, h3848, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3915_1, u3ehi3]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h0, h3333, h3848, h3850, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3915_1, u3ehi3]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3334, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3843, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3848, hlam, p3915_1]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3850, hlam, p3915_1]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3335, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3844, hlam, p3915_0]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h3849, hlam, p3915_1]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [h0, h3335, h3848, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3915_1, u3ehi3]
                                    · have p3915_0 := h3915c.1
                                      have p3915_1 := h3915c.2.1
                                      have p3915_2 := h3915c.2.2.1
                                      have p3915_3 := h3915c.2.2.2
                                      linarith only [hlam, p3915_0]
                                  · rcases h2bigk with h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c | h3957c
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h0, hlam, p3957_1]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h0, h3848, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3957_1, u3ehi3]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      rcases p3957_3 (m.d 0 2) (by simp) with h3961 | h3961
                                      · rcases p3957_3 (m.d 1 2) (by simp) with h3962 | h3962
                                        · rcases p3957_3 (m.d 2 3) (by simp) with h3963 | h3963
                                          · linarith only [h3333, h3963, hlam]
                                          · linarith only [h3848, h3963, hlam]
                                        · linarith only [h3843, h3962, hlam]
                                      · linarith only [h3961, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      rcases p3957_3 (m.d 0 2) (by simp) with h3968 | h3968
                                      · rcases p3957_3 (m.d 1 2) (by simp) with h3969 | h3969
                                        · rcases p3957_3 (m.d 2 3) (by simp) with h3970 | h3970
                                          · linarith only [h3333, h3970, hlam]
                                          · linarith only [h3849, h3970, hlam]
                                        · linarith only [h3844, h3969, hlam]
                                      · linarith only [h3968, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3333, h3849, h3852, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3957_1, u3ehi3]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3849, h3852, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3957_1, u3ehi3]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      rcases p3957_3 (m.d 0 2) (by simp) with h3978 | h3978
                                      · linarith only [h0, h3978, hlam]
                                      · linarith only [h3334, h3978, hlam]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      rcases p3957_3 (m.d 0 2) (by simp) with h3981 | h3981
                                      · linarith only [h0, h3981, hlam]
                                      · linarith only [h3335, h3981, hlam]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3333, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3842, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3333, h3848, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p3957_1, u3ehi3]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h0, h3333, hc12, hlam, hphi, ht01, ht0b, ht5b, p3957_1, u5ehi2]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3334, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3843, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3848, hlam, p3957_1]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3850, hlam, p3957_1]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3335, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3844, hlam, p3957_0]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h3849, hlam, p3957_1]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [h0, h3335, h3848, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3957_1, u3ehi3]
                                    · have p3957_0 := h3957c.1
                                      have p3957_1 := h3957c.2.1
                                      have p3957_2 := h3957c.2.2.1
                                      have p3957_3 := h3957c.2.2.2
                                      linarith only [hlam, p3957_0]
                                  · linarith only [h3338, h3913, hc03, hlam, p3854_1]
                                  · linarith only [h3913, hc03, hlam, p3854_1]
                            · linarith only [h3337, h3908, hlam]
                          · linarith only [h3335, h3907, hlam]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3338, h3847, hc01, hc14, hlam, hphi, p3854_1]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3334, hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3336, hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3338, hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3338, h3847, hc01, hc14, hlam, hphi, p3854_1]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3335, hlam, p3854_1]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3337, hlam, p3854_0]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [h3334, h3338, h3847, h3848, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3854_1, u3ehi3]
                      · have p3854_0 := h3854c.1
                        have p3854_1 := h3854c.2.1
                        have p3854_2 := h3854c.2.2.1
                        have p3854_3 := h3854c.2.2.2
                        linarith only [hlam, p3854_0]
                · linarith only [h3337, h3338, h3842, h3845, h3847, h3848, h3849, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h3336, h3338, h3842, h3845, h3847, h3848, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4015 | h4015
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4016 | h4016
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4017 | h4017
                  · linarith only [h3104, h3847, h4017, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4019 | h4019
                    · linarith only [h3104, h3333, h3847, h4015, h4019, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0bigk with h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c | h4021c
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h0, hlam, p4021_1]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h2914, hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3104, hlam, p4021_1]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3265, hlam, p4021_1]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        rcases p4021_3 (m.d 0 1) (by simp) with h4027 | h4027
                        · linarith only [h0, h4027, hlam]
                        · rcases p4021_3 (m.d 0 2) (by simp) with h4029 | h4029
                          · rcases p4021_3 (m.d 0 3) (by simp) with h4030 | h4030
                            · linarith only [h3333, h4030, hlam]
                            · linarith only [h2914, h4030, hlam]
                          · linarith only [h0, h4029, hlam]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h0, h3333, h4016, h4019, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4021_1, u3ehi3]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        rcases p4021_3 (m.d 0 1) (by simp) with h4036 | h4036
                        · linarith only [h0, h4036, hlam]
                        · rcases p4021_3 (m.d 0 2) (by simp) with h4038 | h4038
                          · rcases p4021_3 (m.d 0 3) (by simp) with h4039 | h4039
                            · linarith only [h3333, h4039, hlam]
                            · linarith only [h3336, h4039, hlam]
                          · linarith only [h3334, h4038, hlam]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        rcases p4021_3 (m.d 0 1) (by simp) with h4043 | h4043
                        · linarith only [h0, h4043, hlam]
                        · rcases p4021_3 (m.d 0 2) (by simp) with h4045 | h4045
                          · rcases p4021_3 (m.d 0 3) (by simp) with h4046 | h4046
                            · linarith only [h3333, h4046, hlam]
                            · linarith only [h3337, h4046, hlam]
                          · linarith only [h3335, h4045, hlam]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        rcases p4021_3 (m.d 0 1) (by simp) with h4050 | h4050
                        · linarith only [h2914, h4050, hlam]
                        · rcases p4021_3 (m.d 0 2) (by simp) with h4052 | h4052
                          · rcases p4021_3 (m.d 0 3) (by simp) with h4053 | h4053
                            · rcases p4021_3 (m.d 0 4) (by simp) with h4054 | h4054
                              · linarith only [h3336, h4054, hlam]
                              · linarith only [h3104, h4054, hlam]
                            · linarith only [h2914, h4053, hlam]
                          · linarith only [h0, h4052, hlam]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3333, hlam, p4021_1]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        rcases p4021_3 (m.d 0 1) (by simp) with h4061 | h4061
                        · linarith only [h2914, h4061, hlam]
                        · rcases p4021_3 (m.d 0 2) (by simp) with h4063 | h4063
                          · rcases p4021_3 (m.d 0 3) (by simp) with h4064 | h4064
                            · rcases p4021_3 (m.d 0 4) (by simp) with h4065 | h4065
                              · linarith only [h3336, h4065, hlam]
                              · rcases p4021_3 (m.d 0 5) (by simp) with h4067 | h4067
                                · linarith only [h3337, h4067, hlam]
                                · linarith only [h3338, h4067, hlam]
                            · linarith only [h3336, h4064, hlam]
                          · linarith only [h3334, h4063, hlam]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        rcases p4021_3 (m.d 0 1) (by simp) with h4072 | h4072
                        · linarith only [h2914, h4072, hlam]
                        · rcases p4021_3 (m.d 0 2) (by simp) with h4074 | h4074
                          · rcases p4021_3 (m.d 0 3) (by simp) with h4075 | h4075
                            · rcases p4021_3 (m.d 0 4) (by simp) with h4076 | h4076
                              · linarith only [h3336, h4076, hlam]
                              · rcases p4021_3 (m.d 0 5) (by simp) with h4078 | h4078
                                · linarith only [h3337, h4078, hlam]
                                · rcases h0emin with h4080 | h4080 | h4080 | h4080 | h4080
                                  · linarith only [h3104, h4080, hc14, hlam, ht01]
                                  · rcases h2bigk with h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c | h4082c
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h0, hlam, p4082_1]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h0, h4016, h4019, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4082_1, u3ehi3]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      rcases p4082_3 (m.d 0 2) (by simp) with h4086 | h4086
                                      · rcases p4082_3 (m.d 1 2) (by simp) with h4087 | h4087
                                        · rcases p4082_3 (m.d 2 3) (by simp) with h4088 | h4088
                                          · linarith only [h3333, h4088, hlam]
                                          · linarith only [h4015, h4088, hlam]
                                        · linarith only [h3843, h4087, hlam]
                                      · linarith only [h4086, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      rcases p4082_3 (m.d 0 2) (by simp) with h4093 | h4093
                                      · rcases p4082_3 (m.d 1 2) (by simp) with h4094 | h4094
                                        · rcases p4082_3 (m.d 2 3) (by simp) with h4095 | h4095
                                          · linarith only [h3333, h4095, hlam]
                                          · linarith only [h4016, h4095, hlam]
                                        · linarith only [h3844, h4094, hlam]
                                      · linarith only [h4093, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h4080, hc12, hlam, ht01, p4082_1]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h4016, h4019, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4082_1, u3ehi3]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      rcases p4082_3 (m.d 0 2) (by simp) with h4103 | h4103
                                      · linarith only [h0, h4103, hlam]
                                      · linarith only [h3334, h4103, hlam]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      rcases p4082_3 (m.d 0 2) (by simp) with h4106 | h4106
                                      · linarith only [h0, h4106, hlam]
                                      · linarith only [h3335, h4106, hlam]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h3333, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h3842, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h3333, h4015, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p4082_1, u3ehi3]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h0, h3333, hc12, hlam, hphi, ht01, ht0b, ht5b, p4082_1, u5ehi2]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h3334, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h3843, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h4015, hlam, p4082_1]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h4017, hlam, p4082_1]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h3335, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h3844, hlam, p4082_0]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h4016, hlam, p4082_1]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [h0, h3335, h4015, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4082_1, u3ehi3]
                                    · have p4082_0 := h4082c.1
                                      have p4082_1 := h4082c.2.1
                                      have p4082_2 := h4082c.2.2.1
                                      have p4082_3 := h4082c.2.2.2
                                      linarith only [hlam, p4082_0]
                                  · rcases h2bigk with h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c | h4124c
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h0, hlam, p4124_1]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h0, h4015, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4124_1, u3ehi3]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      rcases p4124_3 (m.d 0 2) (by simp) with h4128 | h4128
                                      · rcases p4124_3 (m.d 1 2) (by simp) with h4129 | h4129
                                        · rcases p4124_3 (m.d 2 3) (by simp) with h4130 | h4130
                                          · linarith only [h3333, h4130, hlam]
                                          · linarith only [h4015, h4130, hlam]
                                        · linarith only [h3843, h4129, hlam]
                                      · linarith only [h4128, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      rcases p4124_3 (m.d 0 2) (by simp) with h4135 | h4135
                                      · rcases p4124_3 (m.d 1 2) (by simp) with h4136 | h4136
                                        · rcases p4124_3 (m.d 2 3) (by simp) with h4137 | h4137
                                          · linarith only [h3333, h4137, hlam]
                                          · linarith only [h4016, h4137, hlam]
                                        · linarith only [h3844, h4136, hlam]
                                      · linarith only [h4135, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3333, h4016, h4019, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4124_1, u3ehi3]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h4016, h4019, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4124_1, u3ehi3]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      rcases p4124_3 (m.d 0 2) (by simp) with h4145 | h4145
                                      · linarith only [h0, h4145, hlam]
                                      · linarith only [h3334, h4145, hlam]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      rcases p4124_3 (m.d 0 2) (by simp) with h4148 | h4148
                                      · linarith only [h0, h4148, hlam]
                                      · linarith only [h3335, h4148, hlam]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3333, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3842, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3333, h4015, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p4124_1, u3ehi3]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h0, h3333, hc12, hlam, hphi, ht01, ht0b, ht5b, p4124_1, u5ehi2]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3334, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3843, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h4015, hlam, p4124_1]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h4017, hlam, p4124_1]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3335, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h3844, hlam, p4124_0]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h4016, hlam, p4124_1]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [h0, h3335, h4015, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4124_1, u3ehi3]
                                    · have p4124_0 := h4124c.1
                                      have p4124_1 := h4124c.2.1
                                      have p4124_2 := h4124c.2.2.1
                                      have p4124_3 := h4124c.2.2.2
                                      linarith only [hlam, p4124_0]
                                  · linarith only [h3338, h4080, hc03, hlam, p4021_1]
                                  · linarith only [h4080, hc03, hlam, p4021_1]
                            · linarith only [h3337, h4075, hlam]
                          · linarith only [h3335, h4074, hlam]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3104, h3847, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4021_1]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3334, hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3336, hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3338, hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        rcases p4021_3 (m.d 0 1) (by simp) with h4175 | h4175
                        · linarith only [h3265, h4175, hlam]
                        · rcases p4021_3 (m.d 0 2) (by simp) with h4177 | h4177
                          · rcases p4021_3 (m.d 0 3) (by simp) with h4178 | h4178
                            · rcases p4021_3 (m.d 0 4) (by simp) with h4179 | h4179
                              · linarith only [h3338, h4179, hlam]
                              · linarith only [h3104, h4179, hlam]
                            · linarith only [h2914, h4178, hlam]
                          · linarith only [h0, h4177, hlam]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3335, hlam, p4021_1]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3337, hlam, p4021_0]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [h3265, h3336, h3847, hc45, hlam, hphi, ht34, p4021_1, u3ehi3]
                      · have p4021_0 := h4021c.1
                        have p4021_1 := h4021c.2.1
                        have p4021_2 := h4021c.2.2.1
                        have p4021_3 := h4021c.2.2.2
                        linarith only [hlam, p4021_0]
                · linarith only [h0, h3333, h3337, h4015, h4016, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h3104, h3336, h3847, h4015, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h2914, h3333, h3337, h3846, hc01, hc12, hlam, hphi]
        · linarith only [h2914, h3337, h3845, hc34, hlam, hphi, u3ehi4]
      · linarith only [h0, h3333, h3335, h3337, h3844, hlam]
    · linarith only [h0, h3334, h3843, hlam]
  · linarith only [h0, h3333, h3842, hlam]

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3336 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h3337 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h3338 | h3338
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335 h3336 h3337 h3338
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335 h3336 h3337 h3338

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3336 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h3337 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  linarith only [h3336, h3337, hc35, hlam, hphi, u3ehi3]

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3336 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h3337 | h3337
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335 h3336 h3337
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335 h3336 h3337

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3336 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h4196 | h4196
  · linarith only [h3336, h4196, hc34, hlam, hphi, u3ehi4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4198 | h4198
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4199 | h4199
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4200 | h4200
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4201 | h4201
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4202 | h4202
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4203 | h4203
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4204 | h4204
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4205 | h4205
                  · linarith only [h3333, h3336, h4205, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4207 | h4207
                    · linarith only [h3333, h4196, h4207, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4209 | h4209
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4210 | h4210
                        · rcases h0bigk with h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c | h4211c
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h0, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h2914, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3104, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3265, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            rcases p4211_3 (m.d 0 1) (by simp) with h4217 | h4217
                            · linarith only [h0, h4217, hlam]
                            · rcases p4211_3 (m.d 0 2) (by simp) with h4219 | h4219
                              · rcases p4211_3 (m.d 0 3) (by simp) with h4220 | h4220
                                · linarith only [h3333, h4220, hlam]
                                · linarith only [h2914, h4220, hlam]
                              · linarith only [h0, h4219, hlam]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            rcases p4211_3 (m.d 0 1) (by simp) with h4225 | h4225
                            · linarith only [h0, h4225, hlam]
                            · rcases p4211_3 (m.d 0 2) (by simp) with h4227 | h4227
                              · rcases p4211_3 (m.d 0 3) (by simp) with h4228 | h4228
                                · linarith only [h3333, h4228, hlam]
                                · rcases p4211_3 (m.d 0 4) (by simp) with h4230 | h4230
                                  · linarith only [h3334, h4230, hlam]
                                  · linarith only [h3336, h4230, hlam]
                              · linarith only [h3333, h4227, hlam]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h0, h4198, hc12, hlam, hphi, ht01, ht0b, ht5b, p4211_1, u5ehi4]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            rcases p4211_3 (m.d 0 1) (by simp) with h4235 | h4235
                            · linarith only [h0, h4235, hlam]
                            · rcases p4211_3 (m.d 0 2) (by simp) with h4237 | h4237
                              · rcases p4211_3 (m.d 0 3) (by simp) with h4238 | h4238
                                · linarith only [h3333, h4238, hlam]
                                · rcases p4211_3 (m.d 0 4) (by simp) with h4240 | h4240
                                  · linarith only [h3334, h4240, hlam]
                                  · linarith only [h4198, h4240, hlam]
                              · linarith only [h3335, h4237, hlam]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4196, h4203, hc01, hc15, hlam, hphi, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3333, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3336, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4196, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3336, h4199, h4202, hc01, hc12, hlam, hphi, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3334, hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3333, h3336, h4199, h4202, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4211_1, u3ehi2]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3333, h3336, h4196, h4199, h4202, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4211_1, u3ehi2]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3336, h4198, h4199, h4202, hc01, hc12, hlam, hphi, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3335, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h3333, h4196, hc35, hlam, hphi, p4211_1, u3ehi2]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [h4198, hlam, p4211_1]
                          · have p4211_0 := h4211c.1
                            have p4211_1 := h4211c.2.1
                            have p4211_2 := h4211c.2.2.1
                            have p4211_3 := h4211c.2.2.2
                            linarith only [hlam, p4211_0]
                        · linarith only [h0, h3334, h3336, h4198, h4209, h4210, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · linarith only [h3336, h4198, h4205, h4209, hc34, hlam, hphi, u3ehi2]
                · linarith only [h3104, h4196, h4198, h4199, h4203, h4204, hc01, hc12, hlam, hphi]
              · linarith only [h3336, h4198, h4202, h4203, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4263 | h4263
              · linarith only [h4202, h4263, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4265 | h4265
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4266 | h4266
                  · linarith only [h2914, h4202, h4266, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4268 | h4268
                    · linarith only [h2914, h3333, h4202, h4268, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4270 | h4270
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4271 | h4271
                        · rcases h0bigk with h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c | h4272c
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [hlam, p4272_0]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h0, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h2914, hlam, p4272_0]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3104, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3265, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            rcases p4272_3 (m.d 0 1) (by simp) with h4278 | h4278
                            · linarith only [h0, h4278, hlam]
                            · rcases p4272_3 (m.d 0 2) (by simp) with h4280 | h4280
                              · rcases p4272_3 (m.d 0 3) (by simp) with h4281 | h4281
                                · linarith only [h3333, h4281, hlam]
                                · linarith only [h2914, h4281, hlam]
                              · linarith only [h0, h4280, hlam]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [hlam, p4272_0]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            rcases p4272_3 (m.d 0 1) (by simp) with h4286 | h4286
                            · linarith only [h0, h4286, hlam]
                            · rcases p4272_3 (m.d 0 2) (by simp) with h4288 | h4288
                              · rcases p4272_3 (m.d 0 3) (by simp) with h4289 | h4289
                                · linarith only [h3333, h4289, hlam]
                                · rcases p4272_3 (m.d 0 4) (by simp) with h4291 | h4291
                                  · linarith only [h3334, h4291, hlam]
                                  · linarith only [h3336, h4291, hlam]
                              · linarith only [h3333, h4288, hlam]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h0, h3334, h4270, hc12, hlam, hphi, ht01, ht0b, ht5b, p4272_1, u5ehi4]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            rcases p4272_3 (m.d 0 1) (by simp) with h4296 | h4296
                            · linarith only [h0, h4296, hlam]
                            · rcases p4272_3 (m.d 0 2) (by simp) with h4298 | h4298
                              · rcases p4272_3 (m.d 0 3) (by simp) with h4299 | h4299
                                · linarith only [h3333, h4299, hlam]
                                · rcases p4272_3 (m.d 0 4) (by simp) with h4301 | h4301
                                  · linarith only [h3334, h4301, hlam]
                                  · linarith only [h4198, h4301, hlam]
                              · linarith only [h3335, h4298, hlam]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h2914, h4263, h4271, hc01, hc34, hlam, hphi, ht12, ht23, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3333, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [hlam, p4272_0]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3336, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h4196, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            rcases p4272_3 (m.d 0 1) (by simp) with h4310 | h4310
                            · linarith only [h3104, h4310, hlam]
                            · rcases p4272_3 (m.d 0 2) (by simp) with h4312 | h4312
                              · rcases p4272_3 (m.d 0 3) (by simp) with h4313 | h4313
                                · linarith only [h3336, h4313, hlam]
                                · linarith only [h2914, h4313, hlam]
                              · linarith only [h0, h4312, hlam]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3334, hlam, p4272_0]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3104, h4202, hc34, hlam, hphi, p4272_1, u3ehi0]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [hlam, p4272_0]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3104, h3333, h4196, h4202, hc34, hlam, hphi, p4272_1, u3ehi2]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            rcases p4272_3 (m.d 0 1) (by simp) with h4321 | h4321
                            · linarith only [h3265, h4321, hlam]
                            · rcases p4272_3 (m.d 0 2) (by simp) with h4323 | h4323
                              · rcases p4272_3 (m.d 0 3) (by simp) with h4324 | h4324
                                · linarith only [h4196, h4324, hlam]
                                · linarith only [h2914, h4324, hlam]
                              · linarith only [h0, h4323, hlam]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3335, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h3265, h3333, h4263, hc35, hlam, hphi, p4272_1, u3ehi2]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [h4198, hlam, p4272_1]
                          · have p4272_0 := h4272c.1
                            have p4272_1 := h4272c.2.1
                            have p4272_2 := h4272c.2.2.1
                            have p4272_3 := h4272c.2.2.2
                            linarith only [hlam, p4272_0]
                        · linarith only [h3104, h4202, h4270, h4271, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h3336, h4198, h4266, h4270, hc34, hlam, hphi, u3ehi2]
                · linarith only [h3104, h4198, h4265, hlam]
          · linarith only [h0, h3335, h4201, hlam]
        · linarith only [h0, h3334, h4200, hlam]
      · linarith only [h0, h3333, h3335, h3336, h4199, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4338 | h4338
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4339 | h4339
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4340 | h4340
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4341 | h4341
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4342 | h4342
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4343 | h4343
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4344 | h4344
                  · linarith only [h3333, h3336, h4198, h4338, h4341, h4343, h4344, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4346 | h4346
                    · linarith only [h3333, h3336, h4198, h4338, h4341, h4343, h4346, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4348 | h4348
                      · linarith only [h3334, h3336, h4198, h4348, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4350 | h4350
                        · linarith only [h3333, h3336, h4198, h4350, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h3333, h3336, h4338, h4341, h4343, h4350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h3333, h3336, h4341, h4343, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h3333, h3336, h4341, h4342, hc35, hlam, hphi, u3ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4355 | h4355
              · linarith only [h4341, h4355, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4357 | h4357
                · linarith only [h3333, h3336, h4198, h4341, h4357, hc34, hlam, hphi, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4359 | h4359
                  · linarith only [h2914, h3333, h4341, h4357, h4359, hc45, hlam, hphi, ht34, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4361 | h4361
                    · linarith only [h3104, h3333, h3336, h4357, h4361, hc45, hlam, hphi, ht34, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4363 | h4363
                      · linarith only [h2914, h4341, h4357, h4363, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4365 | h4365
                        · linarith only [h2914, h4341, h4357, h4365, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h3333, h3336, h4365, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h3335, h4340, hlam]
        · linarith only [h0, h3334, h4339, hlam]
      · linarith only [h0, h3333, h4338, hlam]

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h3336 | h3336
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335 h3336
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335 h3336

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3335 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h4371 | h4371
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4372 | h4372
    · linarith only [h3333, h3335, h4372, hlam]
    · linarith only [h4371, h4372, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4375 | h4375
    · linarith only [h4371, h4375, hc34, hlam, hphi, u3ehi4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4377 | h4377
      · linarith only [h3334, h3335, h4377, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4379 | h4379
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4380 | h4380
          · rcases m.htr 1 2 5 (by decide) (by decide) with h4381 | h4381
            · linarith only [h3333, h3335, h4381, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h4383 | h4383
              · linarith only [h3333, h4371, h4379, h4381, h4383, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h4385 | h4385
                · linarith only [h3333, h3335, h4375, h4383, h4385, hc34, hlam, hphi, u3ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h4387 | h4387
                  · linarith only [h3104, h4377, h4380, h4381, h4387, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h4389 | h4389
                    · linarith only [h0, h3333, h4381, h4389, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h4391 | h4391
                      · linarith only [h0, h3334, h4381, h4389, h4391, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h3334, h4381, h4389, h4391, hc35, hlam, hphi, u3ehi2]
          · linarith only [h0, h3334, h4380, hlam]
        · linarith only [h0, h3333, h4379, hlam]

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h3335 | h3335
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334 h3335

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3334 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4396 | h4396
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4397 | h4397
    · linarith only [h3333, h3334, h4397, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4399 | h4399
      · linarith only [h4397, h4399, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4401 | h4401
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4402 | h4402
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4403 | h4403
            · linarith only [h3333, h3334, h4403, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4405 | h4405
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4406 | h4406
                · linarith only [h3333, h3334, h4397, h4402, h4403, h4406, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4408 | h4408
                  · linarith only [h3333, h4399, h4406, h4408, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4410 | h4410
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4411 | h4411
                      · linarith only [h3333, h4406, h4411, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h3333, h4403, h4411, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h3104, h4401, h4410, hlam]
              · linarith only [h0, h4396, h4405, hlam]
          · linarith only [h0, h3333, h4402, hlam]
        · linarith only [h3333, h3334, h4401, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4418 | h4418
    · linarith only [h3333, h3334, h4418, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4420 | h4420
      · linarith only [h4418, h4420, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4422 | h4422
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4423 | h4423
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4424 | h4424
            · linarith only [h3333, h3334, h4424, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4426 | h4426
              · linarith only [h3333, h4396, h4424, h4426, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4428 | h4428
                · linarith only [h4418, h4423, h4424, h4428, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4430 | h4430
                  · linarith only [h3333, h4396, h4420, h4428, h4430, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4432 | h4432
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4433 | h4433
                      · linarith only [h3333, h4428, h4433, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h0, h3333, h4424, h4433, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h3104, h4422, h4432, hlam]
          · linarith only [h0, h3333, h4423, hlam]
        · linarith only [h3333, h3334, h4422, hc45, hlam, hphi, ht34, u3ehi2]

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3334 | h3334
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334
  · exact r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 h2914 h3104 h3265 h3333 h3334

set_option maxHeartbeats 5102000 in
set_option maxHeartbeats 5102000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_R_M_IR_s1_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2914 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3104 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3265 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3333 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4439 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.2.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h4440 | h4440
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4441 | h4441
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4442 | h4442
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4443 | h4443
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4444 | h4444
          · linarith only [h3333, h4440, h4444, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4446 | h4446
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4447 | h4447
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4448 | h4448
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4449 | h4449
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4450 | h4450
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4451 | h4451
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4452 | h4452
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4453 | h4453
                          · linarith only [h0, h4439, h4444, h4453, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · linarith only [h0, h4439, h4443, h4444, h4451, h4453, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h4440, h4444, h4452, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4439, h4441, h4443, h4444, h4451, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · linarith only [h3104, h4443, h4450, hlam]
                  · linarith only [h2914, h3333, h4440, h4442, h4449, hlam]
                · linarith only [h2914, h4441, h4448, hlam]
              · linarith only [h0, h4440, h4447, hlam]
            · linarith only [h0, h4439, h4446, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4463 | h4463
          · linarith only [h3333, h4440, h4463, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4465 | h4465
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4466 | h4466
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4467 | h4467
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4468 | h4468
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4469 | h4469
                    · linarith only [h3104, h4443, h4463, h4465, h4469, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4471 | h4471
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4472 | h4472
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4473 | h4473
                          · linarith only [h0, h4439, h4463, h4469, h4473, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4475 | h4475
                            · linarith only [h3104, h4469, h4475, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, hlam, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h2914, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3104, hlam, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3265, hlam, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, h4463, hc01, hc23, hlam, hphi, ht12, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3333, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, h3104, h4463, hc01, hc23, hlam, hphi, ht12, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, h4463, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4477_1, u5ehi0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                rcases p4477_3 (m.d 0 1) (by simp) with h4488 | h4488
                                · linarith only [h2914, h4488, hlam]
                                · rcases p4477_3 (m.d 0 2) (by simp) with h4490 | h4490
                                  · linarith only [h3333, h4490, hlam]
                                  · linarith only [h0, h4490, hlam]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h2914, h4440, h4463, h4471, h4473, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4477_1, u3ehi3]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                rcases p4477_3 (m.d 0 1) (by simp) with h4495 | h4495
                                · linarith only [h2914, h4495, hlam]
                                · rcases p4477_3 (m.d 0 2) (by simp) with h4497 | h4497
                                  · linarith only [h3333, h4497, hlam]
                                  · linarith only [h4439, h4497, hlam]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                rcases p4477_3 (m.d 0 1) (by simp) with h4500 | h4500
                                · linarith only [h2914, h4500, hlam]
                                · rcases p4477_3 (m.d 0 2) (by simp) with h4502 | h4502
                                  · linarith only [h3333, h4502, hlam]
                                  · linarith only [h4440, h4502, hlam]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3104, h4469, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4439, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4441, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4443, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3265, h4463, h4466, hc01, hc23, hlam, hphi, ht12, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4440, hlam, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4442, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3104, h3265, h4463, h4466, hc01, hc23, hlam, hphi, ht12, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                        · linarith only [h0, h4440, h4463, h4472, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4440, h4463, h4471, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h2914, h3265, h4442, h4463, h4466, h4468, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h2914, h4441, h4467, hlam]
              · linarith only [h0, h4440, h4466, hlam]
            · linarith only [h0, h4439, h4465, hlam]
      · linarith only [h4441, h4442, hc35, hlam, hphi, u3ehi3]
    · linarith only [h3333, h4439, h4441, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4523 | h4523
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4524 | h4524
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4525 | h4525
        · linarith only [h4439, h4440, h4525, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4527 | h4527
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4528 | h4528
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4529 | h4529
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4530 | h4530
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4531 | h4531
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4532 | h4532
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4533 | h4533
                      · linarith only [h3333, h4439, h4527, h4533, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3333, h4523, h4525, h4530, h4532, h4533, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4536 | h4536
                      · linarith only [h4439, h4440, h4529, h4536, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3333, h4524, h4536, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h2914, h4524, h4531, hlam]
                · linarith only [h3333, h4524, h4527, h4530, hc34, hlam, hphi, u3ehi4]
              · linarith only [h3333, h4439, h4523, h4527, h4529, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h3333, h4439, h4527, h4528, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4543 | h4543
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4544 | h4544
              · linarith only [h4439, h4440, h4523, h4527, h4544, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4546 | h4546
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4547 | h4547
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4548 | h4548
                    · linarith only [h4523, h4525, h4527, h4543, h4548, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4550 | h4550
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4551 | h4551
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4552 | h4552
                          · linarith only [h0, h4439, h4544, h4548, h4551, h4552, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h4439, h4544, h4550, h4552, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h3333, h4439, h4550, h4551, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h4527, h4550, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h2914, h4523, h4547, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2914, h4523, h4546, hlam]
            · linarith only [h0, h4439, h4543, hlam]
      · linarith only [h4523, h4524, hc35, hlam, hphi, u3ehi3]
    · linarith only [h3333, h4439, h4523, hlam]

end R2N4
