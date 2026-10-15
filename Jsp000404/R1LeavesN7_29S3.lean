import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6334000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_s0_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1951 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2940 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3280 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3841 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3842 | h3842
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3843 | h3843
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3844 | h3844
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3845 | h3845
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3846 | h3846
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3847 | h3847
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3848 | h3848
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3849 | h3849
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3850 | h3850
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3851 | h3851
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3852 | h3852
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3853 | h3853
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3854 | h3854
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3855 | h3855
                            · linarith only [h3841, h3852, h3855, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h3842, h3854, h3855, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3858 | h3858
                            · linarith only [h3844, h3854, h3858, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c | h3860c
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h0, hlam, p3860_1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h1951, hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h2940, hlam, p3860_1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3280, hlam, p3860_1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                rcases p3860_3 (m.d 0 1) (by simp) with h3866 | h3866
                                · linarith only [h0, h3866, hlam]
                                · rcases p3860_3 (m.d 0 2) (by simp) with h3868 | h3868
                                  · rcases p3860_3 (m.d 0 3) (by simp) with h3869 | h3869
                                    · linarith only [h3841, h3869, hlam]
                                    · linarith only [h1951, h3869, hlam]
                                  · linarith only [h0, h3868, hlam]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3841, h3853, hc35, hlam, hphi, ht0b, ht5b, p3860_1, u0elo1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3846, h3852, h3854, hc34, hlam, hphi, ht0b, ht45, ht5b, p3860_1, u0elo1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3846, h3852, h3854, hc34, hlam, hphi, ht0b, ht45, ht5b, p3860_1, u0elo1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                rcases p3860_3 (m.d 0 1) (by simp) with h3877 | h3877
                                · linarith only [h1951, h3877, hlam]
                                · rcases p3860_3 (m.d 0 2) (by simp) with h3879 | h3879
                                  · rcases p3860_3 (m.d 0 3) (by simp) with h3880 | h3880
                                    · rcases p3860_3 (m.d 0 4) (by simp) with h3881 | h3881
                                      · linarith only [h3844, h3881, hlam]
                                      · linarith only [h2940, h3881, hlam]
                                    · linarith only [h1951, h3880, hlam]
                                  · linarith only [h0, h3879, hlam]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3841, hlam, p3860_1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3846, h3852, h3854, hc34, hlam, hphi, ht0b, ht45, ht5b, p3860_1, u0elo2]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3841, h3846, h3852, h3854, hc34, hlam, hphi, ht0b, ht45, ht5b, p3860_1, u0elo1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                rcases p3860_3 (m.d 0 1) (by simp) with h3890 | h3890
                                · linarith only [h2940, h3890, hlam]
                                · rcases p3860_3 (m.d 0 2) (by simp) with h3892 | h3892
                                  · rcases p3860_3 (m.d 0 3) (by simp) with h3893 | h3893
                                    · rcases p3860_3 (m.d 0 4) (by simp) with h3894 | h3894
                                      · rcases p3860_3 (m.d 0 5) (by simp) with h3895 | h3895
                                        · linarith only [h3846, h3895, hlam]
                                        · linarith only [h3280, h3895, hlam]
                                      · linarith only [h2940, h3894, hlam]
                                    · linarith only [h1951, h3893, hlam]
                                  · linarith only [h0, h3892, hlam]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3842, hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3844, hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3846, h3852, h3854, hc34, hlam, hphi, ht0b, ht45, ht5b, p3860_1, u0elo3]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3860_1, u5elo0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3843, hlam, p3860_1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3845, hlam, p3860_0]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [h3846, hlam, p3860_1]
                              · have p3860_0 := h3860c.1
                                have p3860_1 := h3860c.2.1
                                have p3860_2 := h3860c.2.2.1
                                have p3860_3 := h3860c.2.2.2
                                linarith only [hlam, p3860_0]
                        · linarith only [h3841, h3845, h3852, h3853, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3911 | h3911
                        · linarith only [h3841, h3844, h3852, h3911, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3913 | h3913
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3914 | h3914
                            · rcases h0bigk with h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c | h3915c
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
                                linarith only [h1951, hlam, p3915_0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h2940, hlam, p3915_1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3280, hlam, p3915_1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                rcases p3915_3 (m.d 0 1) (by simp) with h3921 | h3921
                                · linarith only [h0, h3921, hlam]
                                · rcases p3915_3 (m.d 0 2) (by simp) with h3923 | h3923
                                  · rcases p3915_3 (m.d 0 3) (by simp) with h3924 | h3924
                                    · linarith only [h3841, h3924, hlam]
                                    · linarith only [h1951, h3924, hlam]
                                  · linarith only [h0, h3923, hlam]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [hlam, p3915_0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3844, h3911, h3914, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3915_1, u0elo1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3842, h3913, hc45, hlam, hphi, ht0b, ht5b, p3915_1, u0elo1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3845, h3911, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3915_1, u0elo1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                rcases p3915_3 (m.d 0 1) (by simp) with h3932 | h3932
                                · linarith only [h1951, h3932, hlam]
                                · rcases p3915_3 (m.d 0 2) (by simp) with h3934 | h3934
                                  · rcases p3915_3 (m.d 0 3) (by simp) with h3935 | h3935
                                    · rcases p3915_3 (m.d 0 4) (by simp) with h3936 | h3936
                                      · linarith only [h3844, h3936, hlam]
                                      · linarith only [h2940, h3936, hlam]
                                    · linarith only [h1951, h3935, hlam]
                                  · linarith only [h0, h3934, hlam]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3841, hlam, p3915_1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [hlam, p3915_0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3844, h3911, h3914, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3915_1, u0elo2]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3841, h3845, h3911, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3915_1, u0elo1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                rcases p3915_3 (m.d 0 1) (by simp) with h3945 | h3945
                                · linarith only [h2940, h3945, hlam]
                                · rcases p3915_3 (m.d 0 2) (by simp) with h3947 | h3947
                                  · rcases p3915_3 (m.d 0 3) (by simp) with h3948 | h3948
                                    · rcases p3915_3 (m.d 0 4) (by simp) with h3949 | h3949
                                      · rcases p3915_3 (m.d 0 5) (by simp) with h3950 | h3950
                                        · linarith only [h3846, h3950, hlam]
                                        · linarith only [h3280, h3950, hlam]
                                      · linarith only [h2940, h3949, hlam]
                                    · linarith only [h1951, h3948, hlam]
                                  · linarith only [h0, h3947, hlam]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3842, hlam, p3915_0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3844, hlam, p3915_0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [hlam, p3915_0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3845, h3911, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3915_1, u0elo3]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3915_1, u5elo0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3843, hlam, p3915_1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3845, hlam, p3915_0]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [h3846, hlam, p3915_1]
                              · have p3915_0 := h3915c.1
                                have p3915_1 := h3915c.2.1
                                have p3915_2 := h3915c.2.2.1
                                have p3915_3 := h3915c.2.2.2
                                linarith only [hlam, p3915_0]
                            · linarith only [h3842, h3913, h3914, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3966 | h3966
                            · linarith only [h3841, h3844, h3852, h3913, h3966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h3841, h3844, h3846, h3852, h3966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1951, h3844, h3846, h3851, hc45, hlam, hphi, u5elo3]
                  · linarith only [h1951, h3844, h3850, hlam]
                · linarith only [h0, h3841, h3844, h3849, hc34, hlam, hphi, ht45, u5elo2]
              · linarith only [h1951, h3842, h3847, h3848, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h3841, h3847, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3974 | h3974
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3975 | h3975
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3976 | h3976
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3977 | h3977
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3978 | h3978
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3979 | h3979
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3980 | h3980
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3981 | h3981
                          · linarith only [h3842, h3846, h3981, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3983 | h3983
                            · linarith only [h3841, h3846, h3979, h3983, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h0, hlam, p3985_1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h1951, hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h2940, hlam, p3985_1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3280, hlam, p3985_1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                rcases p3985_3 (m.d 0 1) (by simp) with h3991 | h3991
                                · linarith only [h0, h3991, hlam]
                                · rcases p3985_3 (m.d 0 2) (by simp) with h3993 | h3993
                                  · rcases p3985_3 (m.d 0 3) (by simp) with h3994 | h3994
                                    · linarith only [h3841, h3994, hlam]
                                    · linarith only [h1951, h3994, hlam]
                                  · linarith only [h0, h3993, hlam]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3841, h3980, hc35, hlam, hphi, ht0b, ht5b, p3985_1, u0elo1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                rcases p3985_3 (m.d 0 1) (by simp) with h4000 | h4000
                                · linarith only [h0, h4000, hlam]
                                · rcases p3985_3 (m.d 0 2) (by simp) with h4002 | h4002
                                  · rcases p3985_3 (m.d 0 3) (by simp) with h4003 | h4003
                                    · linarith only [h3841, h4003, hlam]
                                    · linarith only [h3844, h4003, hlam]
                                  · linarith only [h3842, h4002, hlam]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                rcases p3985_3 (m.d 0 1) (by simp) with h4007 | h4007
                                · linarith only [h0, h4007, hlam]
                                · rcases p3985_3 (m.d 0 2) (by simp) with h4009 | h4009
                                  · rcases p3985_3 (m.d 0 3) (by simp) with h4010 | h4010
                                    · linarith only [h3841, h4010, hlam]
                                    · linarith only [h3845, h4010, hlam]
                                  · linarith only [h3843, h4009, hlam]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                rcases p3985_3 (m.d 0 1) (by simp) with h4014 | h4014
                                · linarith only [h1951, h4014, hlam]
                                · rcases p3985_3 (m.d 0 2) (by simp) with h4016 | h4016
                                  · rcases p3985_3 (m.d 0 3) (by simp) with h4017 | h4017
                                    · rcases p3985_3 (m.d 0 4) (by simp) with h4018 | h4018
                                      · linarith only [h3844, h4018, hlam]
                                      · linarith only [h2940, h4018, hlam]
                                    · linarith only [h1951, h4017, hlam]
                                  · linarith only [h0, h4016, hlam]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3841, hlam, p3985_1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                rcases p3985_3 (m.d 0 1) (by simp) with h4025 | h4025
                                · linarith only [h1951, h4025, hlam]
                                · rcases p3985_3 (m.d 0 2) (by simp) with h4027 | h4027
                                  · rcases p3985_3 (m.d 0 3) (by simp) with h4028 | h4028
                                    · rcases p3985_3 (m.d 0 4) (by simp) with h4029 | h4029
                                      · linarith only [h3844, h4029, hlam]
                                      · rcases p3985_3 (m.d 0 5) (by simp) with h4031 | h4031
                                        · linarith only [h3845, h4031, hlam]
                                        · linarith only [h3846, h4031, hlam]
                                    · linarith only [h3844, h4028, hlam]
                                  · linarith only [h3842, h4027, hlam]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                rcases p3985_3 (m.d 0 1) (by simp) with h4036 | h4036
                                · linarith only [h1951, h4036, hlam]
                                · rcases p3985_3 (m.d 0 2) (by simp) with h4038 | h4038
                                  · rcases p3985_3 (m.d 0 3) (by simp) with h4039 | h4039
                                    · rcases p3985_3 (m.d 0 4) (by simp) with h4040 | h4040
                                      · linarith only [h3844, h4040, hlam]
                                      · rcases p3985_3 (m.d 0 5) (by simp) with h4042 | h4042
                                        · linarith only [h3845, h4042, hlam]
                                        · rcases h2bigk with h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c | h4044c
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h0, hlam, p4044_1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3980, h3983, hc34, hlam, hphi, ht0b, ht45, ht5b, p4044_1, u0elo1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            rcases p4044_3 (m.d 0 2) (by simp) with h4048 | h4048
                                            · rcases p4044_3 (m.d 1 2) (by simp) with h4049 | h4049
                                              · rcases p4044_3 (m.d 2 3) (by simp) with h4050 | h4050
                                                · linarith only [h3841, h4050, hlam]
                                                · linarith only [h3979, h4050, hlam]
                                              · linarith only [h3975, h4049, hlam]
                                            · linarith only [h4048, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            rcases p4044_3 (m.d 0 2) (by simp) with h4055 | h4055
                                            · rcases p4044_3 (m.d 1 2) (by simp) with h4056 | h4056
                                              · rcases p4044_3 (m.d 2 3) (by simp) with h4057 | h4057
                                                · linarith only [h3841, h4057, hlam]
                                                · linarith only [h3980, h4057, hlam]
                                              · linarith only [h3976, h4056, hlam]
                                            · linarith only [h4055, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3841, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3985_1, p4044_1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            rcases p4044_3 (m.d 0 2) (by simp) with h4064 | h4064
                                            · linarith only [h0, h4064, hlam]
                                            · linarith only [h3841, h4064, hlam]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            rcases p4044_3 (m.d 0 2) (by simp) with h4067 | h4067
                                            · linarith only [h0, h4067, hlam]
                                            · linarith only [h3842, h4067, hlam]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            rcases p4044_3 (m.d 0 2) (by simp) with h4070 | h4070
                                            · linarith only [h0, h4070, hlam]
                                            · linarith only [h3843, h4070, hlam]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3841, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3974, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3841, hc24, hlam, hphi, ht0b, ht45, ht5b, p4044_1, u0elo1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3841, h3980, h3983, hc34, hlam, hphi, ht0b, ht45, ht5b, p4044_1, u0elo1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3842, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3975, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3979, hlam, p4044_1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3981, hlam, p4044_1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3843, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3976, hlam, p4044_0]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3980, hlam, p4044_1]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [h3979, hc34, hlam, hphi, ht45, p4044_1, u5elo2]
                                          · have p4044_0 := h4044c.1
                                            have p4044_1 := h4044c.2.1
                                            have p4044_2 := h4044c.2.2.1
                                            have p4044_3 := h4044c.2.2.2
                                            linarith only [hlam, p4044_0]
                                    · linarith only [h3845, h4039, hlam]
                                  · linarith only [h3843, h4038, hlam]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3846, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p3985_1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3842, hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3844, hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3846, hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3280, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3985_1, u5elo1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3843, hlam, p3985_1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3845, hlam, p3985_0]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [h3280, hc04, hlam, hphi, ht45, p3985_1, u5elo1]
                              · have p3985_0 := h3985c.1
                                have p3985_1 := h3985c.2.1
                                have p3985_2 := h3985c.2.2.1
                                have p3985_3 := h3985c.2.2.2
                                linarith only [hlam, p3985_0]
                        · linarith only [h3841, h3845, h3979, h3980, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h3844, h3846, h3979, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h1951, h3845, h3978, hlam]
                  · linarith only [h1951, h3844, h3846, h3977, hc03, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h0, h3280, h3843, h3976, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
              · linarith only [h0, h3842, h3975, hlam]
            · linarith only [h0, h3841, h3974, hlam]
        · linarith only [h3844, h3845, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4108 | h4108
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4109 | h4109
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4110 | h4110
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4111 | h4111
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4112 | h4112
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4113 | h4113
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4114 | h4114
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4115 | h4115
                      · linarith only [h3841, h3844, h4108, h4115, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4117 | h4117
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4118 | h4118
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4119 | h4119
                            · rcases h0bigk with h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [hlam, p4120_0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h0, hlam, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h1951, hlam, p4120_0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h2940, hlam, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3280, hlam, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                rcases p4120_3 (m.d 0 1) (by simp) with h4126 | h4126
                                · linarith only [h0, h4126, hlam]
                                · rcases p4120_3 (m.d 0 2) (by simp) with h4128 | h4128
                                  · rcases p4120_3 (m.d 0 3) (by simp) with h4129 | h4129
                                    · linarith only [h3841, h4129, hlam]
                                    · linarith only [h1951, h4129, hlam]
                                  · linarith only [h0, h4128, hlam]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [hlam, p4120_0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3841, h4117, h4119, hc45, hlam, hphi, ht0b, ht5b, p4120_1, u0elo1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3841, h3844, h4117, h4119, hc45, hlam, hphi, ht0b, ht5b, p4120_1, u0elo1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                rcases p4120_3 (m.d 0 1) (by simp) with h4136 | h4136
                                · linarith only [h0, h4136, hlam]
                                · rcases p4120_3 (m.d 0 2) (by simp) with h4138 | h4138
                                  · rcases p4120_3 (m.d 0 3) (by simp) with h4139 | h4139
                                    · linarith only [h3841, h4139, hlam]
                                    · linarith only [h4108, h4139, hlam]
                                  · linarith only [h3843, h4138, hlam]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3844, h4110, h4113, hc01, hc12, hlam, hphi, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3841, hlam, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [hlam, p4120_0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3844, hlam, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3844, h4110, h4113, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3844, h4110, h4113, hc01, hc12, hlam, hphi, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3842, hlam, p4120_0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h1951, h3844, h4110, h4113, hc01, hc12, hlam, hphi, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [hlam, p4120_0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3280, h3844, h4110, h4113, hc01, hc12, hlam, hphi, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4120_1, u5elo0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h3843, hlam, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h4108, hlam, p4120_0]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [h4109, hlam, p4120_1]
                              · have p4120_0 := h4120c.1
                                have p4120_1 := h4120c.2.1
                                have p4120_2 := h4120c.2.2.1
                                have p4120_3 := h4120c.2.2.2
                                linarith only [hlam, p4120_0]
                            · linarith only [h3844, h4119, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h4109, h4115, h4117, h4118, hc35, hlam, hphi, u5elo0]
                        · linarith only [h3844, h4108, h4110, h4113, h4117, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h3844, h4108, h4113, h4114, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4162 | h4162
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4163 | h4163
                      · linarith only [h3280, h4113, h4162, h4163, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4165 | h4165
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4166 | h4166
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4167 | h4167
                            · rcases h0bigk with h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c | h4168c
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [hlam, p4168_0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h0, hlam, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h1951, hlam, p4168_0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h2940, hlam, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3280, hlam, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                rcases p4168_3 (m.d 0 1) (by simp) with h4174 | h4174
                                · linarith only [h0, h4174, hlam]
                                · rcases p4168_3 (m.d 0 2) (by simp) with h4176 | h4176
                                  · rcases p4168_3 (m.d 0 3) (by simp) with h4177 | h4177
                                    · linarith only [h3841, h4177, hlam]
                                    · linarith only [h1951, h4177, hlam]
                                  · linarith only [h0, h4176, hlam]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [hlam, p4168_0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3841, h4165, hc35, hlam, hphi, ht0b, ht5b, p4168_1, u0elo1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3842, h4163, h4165, h4167, hc45, hlam, hphi, ht0b, ht5b, p4168_1, u0elo1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                rcases p4168_3 (m.d 0 1) (by simp) with h4184 | h4184
                                · linarith only [h0, h4184, hlam]
                                · rcases p4168_3 (m.d 0 2) (by simp) with h4186 | h4186
                                  · rcases p4168_3 (m.d 0 3) (by simp) with h4187 | h4187
                                    · linarith only [h3841, h4187, hlam]
                                    · linarith only [h4108, h4187, hlam]
                                  · linarith only [h3843, h4186, hlam]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h1951, h4113, hc01, hc34, hlam, hphi, ht12, ht23, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3841, hlam, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [hlam, p4168_0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3844, hlam, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h1951, h3280, h4113, hc01, hc34, hlam, hphi, ht12, ht23, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                rcases p4168_3 (m.d 0 1) (by simp) with h4196 | h4196
                                · linarith only [h2940, h4196, hlam]
                                · rcases p4168_3 (m.d 0 2) (by simp) with h4198 | h4198
                                  · rcases p4168_3 (m.d 0 3) (by simp) with h4199 | h4199
                                    · linarith only [h3844, h4199, hlam]
                                    · linarith only [h1951, h4199, hlam]
                                  · linarith only [h0, h4198, hlam]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3842, hlam, p4168_0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3841, h3842, h4165, h4167, hc45, hlam, hphi, ht0b, ht5b, p4168_1, u0elo1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [hlam, p4168_0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                rcases p4168_3 (m.d 0 1) (by simp) with h4206 | h4206
                                · linarith only [h2940, h4206, hlam]
                                · rcases p4168_3 (m.d 0 2) (by simp) with h4208 | h4208
                                  · rcases p4168_3 (m.d 0 3) (by simp) with h4209 | h4209
                                    · linarith only [h3844, h4209, hlam]
                                    · linarith only [h4108, h4209, hlam]
                                  · linarith only [h3843, h4208, hlam]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4168_1, u5elo0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h3843, hlam, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h4108, hlam, p4168_0]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [h4109, hlam, p4168_1]
                              · have p4168_0 := h4168c.1
                                have p4168_1 := h4168c.2.1
                                have p4168_2 := h4168c.2.2.1
                                have p4168_3 := h4168c.2.2.2
                                linarith only [hlam, p4168_0]
                            · linarith only [h4113, h4167, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h3280, h4109, h4163, h4165, h4166, hc35, hlam, hphi, u5elo1]
                        · linarith only [h1951, h4108, h4113, h4165, hc23, hc34, hlam, hphi]
                    · linarith only [h1951, h4108, h4162, hlam]
                · linarith only [h0, h4112, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3842, h4111, hlam]
            · linarith only [h0, h3841, h4110, hlam]
          · linarith only [h3844, h4108, h4109, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4226 | h4226
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4227 | h4227
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4228 | h4228
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4229 | h4229
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4230 | h4230
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4231 | h4231
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4232 | h4232
                      · linarith only [h3841, h3844, h4232, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4234 | h4234
                        · linarith only [h3841, h4108, h4234, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4236 | h4236
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4237 | h4237
                            · rcases h0bigk with h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c | h4238c
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [hlam, p4238_0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h0, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h1951, hlam, p4238_0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h2940, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3280, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                rcases p4238_3 (m.d 0 1) (by simp) with h4244 | h4244
                                · linarith only [h0, h4244, hlam]
                                · rcases p4238_3 (m.d 0 2) (by simp) with h4246 | h4246
                                  · rcases p4238_3 (m.d 0 3) (by simp) with h4247 | h4247
                                    · linarith only [h3841, h4247, hlam]
                                    · linarith only [h1951, h4247, hlam]
                                  · linarith only [h0, h4246, hlam]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [hlam, p4238_0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                rcases p4238_3 (m.d 0 1) (by simp) with h4252 | h4252
                                · linarith only [h0, h4252, hlam]
                                · rcases p4238_3 (m.d 0 2) (by simp) with h4254 | h4254
                                  · rcases p4238_3 (m.d 0 3) (by simp) with h4255 | h4255
                                    · linarith only [h3841, h4255, hlam]
                                    · rcases p4238_3 (m.d 0 4) (by simp) with h4257 | h4257
                                      · linarith only [h3842, h4257, hlam]
                                      · linarith only [h3844, h4257, hlam]
                                  · linarith only [h3841, h4254, hlam]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3842, h4236, hc45, hlam, hphi, ht0b, ht5b, p4238_1, u0elo1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                rcases p4238_3 (m.d 0 1) (by simp) with h4262 | h4262
                                · linarith only [h0, h4262, hlam]
                                · rcases p4238_3 (m.d 0 2) (by simp) with h4264 | h4264
                                  · rcases p4238_3 (m.d 0 3) (by simp) with h4265 | h4265
                                    · linarith only [h3841, h4265, hlam]
                                    · rcases p4238_3 (m.d 0 4) (by simp) with h4267 | h4267
                                      · linarith only [h3842, h4267, hlam]
                                      · linarith only [h4226, h4267, hlam]
                                  · linarith only [h3843, h4264, hlam]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h4108, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4238_1, u5elo0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3841, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [hlam, p4238_0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3844, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h4108, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3844, h4227, h4230, hc01, hc12, hlam, hphi, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3842, hlam, p4238_0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h1951, h3844, h4227, h4230, hc01, hc12, hlam, hphi, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [hlam, p4238_0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3280, h3844, h4227, h4230, hc01, hc12, hlam, hphi, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4238_1, u5elo0]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h3843, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h1951, h4108, h4231, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4238_1, u5elo1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [h4226, hlam, p4238_1]
                              · have p4238_0 := h4238c.1
                                have p4238_1 := h4238c.2.1
                                have p4238_2 := h4238c.2.2.1
                                have p4238_3 := h4238c.2.2.2
                                linarith only [hlam, p4238_0]
                            · linarith only [h1951, h3844, h4237, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4287 | h4287
                            · rcases h0bigk with h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c | h4288c
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [hlam, p4288_0]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h0, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h1951, hlam, p4288_0]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h2940, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3280, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                rcases p4288_3 (m.d 0 1) (by simp) with h4294 | h4294
                                · linarith only [h0, h4294, hlam]
                                · rcases p4288_3 (m.d 0 2) (by simp) with h4296 | h4296
                                  · rcases p4288_3 (m.d 0 3) (by simp) with h4297 | h4297
                                    · linarith only [h3841, h4297, hlam]
                                    · linarith only [h1951, h4297, hlam]
                                  · linarith only [h0, h4296, hlam]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [hlam, p4288_0]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                rcases p4288_3 (m.d 0 1) (by simp) with h4302 | h4302
                                · linarith only [h0, h4302, hlam]
                                · rcases p4288_3 (m.d 0 2) (by simp) with h4304 | h4304
                                  · rcases p4288_3 (m.d 0 3) (by simp) with h4305 | h4305
                                    · linarith only [h3841, h4305, hlam]
                                    · rcases p4288_3 (m.d 0 4) (by simp) with h4307 | h4307
                                      · linarith only [h3842, h4307, hlam]
                                      · linarith only [h3844, h4307, hlam]
                                  · linarith only [h3841, h4304, hlam]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h4226, h4232, h4236, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4288_1, u0elo1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h4226, h4232, h4236, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4288_1, u0elo1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3844, h4227, h4230, hc01, hc12, hlam, hphi, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3841, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [hlam, p4288_0]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3844, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h4108, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3844, h4227, h4230, hc01, hc12, hlam, hphi, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3842, hlam, p4288_0]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h1951, h3844, h4227, h4230, hc01, hc12, hlam, hphi, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [hlam, p4288_0]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3280, h3844, h4227, h4230, hc01, hc12, hlam, hphi, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3844, h4226, h4227, h4230, h4232, h4236, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p4288_1, u5elo0]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h3843, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h1951, h3844, h4108, h4226, h4227, h4230, h4231, h4232, h4236, hc01, hc12, hc23, hlam, hphi, ht34, ht45, p4288_1, u5elo1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [h4226, hlam, p4288_1]
                              · have p4288_0 := h4288c.1
                                have p4288_1 := h4288c.2.1
                                have p4288_2 := h4288c.2.2.1
                                have p4288_3 := h4288c.2.2.2
                                linarith only [hlam, p4288_0]
                            · linarith only [h3844, h4226, h4287, hlam]
                    · linarith only [h3844, h4230, h4231, hc04, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4330 | h4330
                    · linarith only [h1951, h4108, h4230, h4330, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1951, h4330, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h4229, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3842, h4228, hlam]
            · linarith only [h0, h3841, h4227, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4336 | h4336
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4337 | h4337
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4338 | h4338
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4339 | h4339
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4340 | h4340
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4341 | h4341
                      · linarith only [h1951, h3841, h3844, h4341, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4343 | h4343
                        · linarith only [h3841, h3844, h4108, h4226, h4343, hc05, hlam, hphi, u5elo4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4345 | h4345
                          · linarith only [h3842, h4226, h4345, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4347 | h4347
                            · linarith only [h1951, h3844, h4226, h4339, h4347, hc01, hc13, hlam, hphi]
                            · linarith only [h1951, h3844, h4347, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · linarith only [h1951, h4340, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4351 | h4351
                    · linarith only [h1951, h4108, h4339, h4351, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1951, h4351, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h3843, h4338, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h0, h3842, h4337, hlam]
            · linarith only [h0, h3841, h4336, hlam]
    · linarith only [h3841, h3843, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4358 | h4358
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4359 | h4359
      · linarith only [h3841, h3842, h4359, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4361 | h4361
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4362 | h4362
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4363 | h4363
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4364 | h4364
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4365 | h4365
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4366 | h4366
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4367 | h4367
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4368 | h4368
                      · linarith only [h3841, h4359, h4368, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4370 | h4370
                        · linarith only [h3841, h3842, h4366, h4368, h4370, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h3841, h3842, h4361, h4363, h4366, h4368, h4370, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h3841, h3842, h4361, h4366, h4367, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4374 | h4374
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4375 | h4375
                      · linarith only [h3841, h3842, h4364, h4366, h4375, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4377 | h4377
                        · linarith only [h3841, h3842, h4364, h4377, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h3841, h3842, h4361, h4364, h4377, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h3841, h3842, h4361, h4364, h4374, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h3842, h4358, h4364, h4365, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4382 | h4382
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4383 | h4383
                  · linarith only [h4359, h4361, h4363, h4364, h4383, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4385 | h4385
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4386 | h4386
                      · linarith only [h2940, h3841, h4383, h4386, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4388 | h4388
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4389 | h4389
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4390 | h4390
                            · rcases h0bigk with h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c | h4391c
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [hlam, p4391_0]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h0, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h1951, hlam, p4391_0]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h2940, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h3280, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h0, h4364, h4386, hc01, hc34, hlam, hphi, ht12, ht23, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [hlam, p4391_0]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h0, h3841, h4364, h4386, h4388, h4390, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h3842, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h0, h3280, h4364, h4386, hc01, hc34, hlam, hphi, ht12, ht23, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h1951, h4363, h4364, h4386, hc01, hc34, hlam, hphi, ht12, ht23, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h3841, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [hlam, p4391_0]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h4359, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h1951, h3280, h4363, h4364, h4386, hc01, hc34, hlam, hphi, ht12, ht23, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                rcases p4391_3 (m.d 0 1) (by simp) with h4407 | h4407
                                · linarith only [h2940, h4407, hlam]
                                · rcases p4391_3 (m.d 0 2) (by simp) with h4409 | h4409
                                  · linarith only [h3842, h4409, hlam]
                                  · linarith only [h0, h4409, hlam]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h3841, h4388, h4390, hc45, hlam, hphi, ht0b, ht5b, p4391_1, u0elo3]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h3841, h4388, h4390, hc45, hlam, hphi, ht0b, ht5b, p4391_1, u0elo3]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [hlam, p4391_0]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                rcases p4391_3 (m.d 0 1) (by simp) with h4415 | h4415
                                · linarith only [h2940, h4415, hlam]
                                · rcases p4391_3 (m.d 0 2) (by simp) with h4417 | h4417
                                  · linarith only [h3842, h4417, hlam]
                                  · linarith only [h4358, h4417, hlam]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4391_1, u5elo0]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h4358, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h4361, hlam, p4391_0]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [h4362, hlam, p4391_1]
                              · have p4391_0 := h4391c.1
                                have p4391_1 := h4391c.2.1
                                have p4391_2 := h4391c.2.2.1
                                have p4391_3 := h4391c.2.2.2
                                linarith only [hlam, p4391_0]
                            · linarith only [h0, h3841, h4364, h4386, h4388, h4390, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h3280, h3841, h4362, h4364, h4388, h4389, hc35, hlam, hphi, u5elo1]
                        · linarith only [h1951, h4361, h4363, h4364, h4386, h4388, hc23, hc34, hlam, hphi]
                    · linarith only [h1951, h4361, h4385, hlam]
                · linarith only [h0, h4382, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h3841, h4363, hlam]
          · linarith only [h3841, h3842, h4362, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4432 | h4432
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4433 | h4433
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4434 | h4434
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4435 | h4435
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4436 | h4436
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4437 | h4437
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4438 | h4438
                      · linarith only [h1951, h3841, h4359, h4438, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4440 | h4440
                        · linarith only [h1951, h3841, h3842, h4361, h4433, h4436, h4438, h4440, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4442 | h4442
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4443 | h4443
                            · rcases h0bigk with h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c | h4444c
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [hlam, p4444_0]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h0, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h1951, hlam, p4444_0]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h2940, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h3280, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h3842, h4433, h4436, h4438, hc01, hc12, hlam, hphi, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [hlam, p4444_0]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h1951, h3842, h4433, h4436, h4438, hc01, hc12, hlam, hphi, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h3842, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h1951, h3842, h4361, h4433, h4436, h4437, h4438, hc01, hc05, hc12, hlam, hphi, p4444_1, u5elo1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h4361, h4437, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4444_1, u5elo1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h3841, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [hlam, p4444_0]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h4359, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h4361, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h3842, h4433, h4436, h4438, hc01, hc12, hlam, hphi, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h3842, h4358, h4433, h4436, h4438, h4440, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h1951, h3842, h4433, h4436, h4438, hc01, hc12, hlam, hphi, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [hlam, p4444_0]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h1951, h3842, h4361, h4433, h4436, h4438, hc01, hc12, hlam, hphi, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p4444_1, u5elo0]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h4358, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h1951, h3842, h4358, h4433, h4436, h4438, hc01, hc12, hlam, hphi, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [h4432, hlam, p4444_1]
                              · have p4444_0 := h4444c.1
                                have p4444_1 := h4444c.2.1
                                have p4444_2 := h4444c.2.2.1
                                have p4444_3 := h4444c.2.2.2
                                linarith only [hlam, p4444_0]
                            · linarith only [h3842, h4358, h4438, h4442, h4443, hlam]
                          · linarith only [h3842, h4358, h4440, h4442, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h4436, h4437, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4473 | h4473
                    · linarith only [h1951, h4361, h4436, h4473, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1951, h4473, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h3842, h4358, h4434, h4435, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4477 | h4477
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4478 | h4478
                  · linarith only [h1951, h4359, h4433, h4434, h4478, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4480 | h4480
                    · linarith only [h1951, h4361, h4433, h4434, h4480, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h1951, h4480, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h4358, h4477, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h3841, h4433, hlam]
          · linarith only [h3842, h4358, h4432, hc25, hlam, hphi, u5elo4]
    · linarith only [h3841, h4358, hc23, hlam, hphi, ht34, ht45, u5elo2]

end R2N4
