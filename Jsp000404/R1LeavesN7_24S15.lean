import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h3889 | h3889
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3890 | h3890
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3891 | h3891
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3892 | h3892
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3893 | h3893
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3894 | h3894
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3895 | h3895
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3896 | h3896
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3897 | h3897
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3898 | h3898
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3899 | h3899
                      · linarith only [h0, h3888, h3899, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3888, h3894, h3899, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3892, h3898, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h3891, h3897, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3904 | h3904
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3905 | h3905
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3906 | h3906
                      · linarith only [h0, h3888, h3906, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3888, h3894, h3906, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3892, h3905, hlam]
                  · linarith only [h0, h3891, h3904, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3911 | h3911
                · linarith only [h3894, h3895, h3911, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3913 | h3913
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3914 | h3914
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3915 | h3915
                      · linarith only [h0, h3888, h3915, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3890, h3894, h3895, h3915, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3892, h3914, hlam]
                  · linarith only [h0, h3891, h3913, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3920 | h3920
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3921 | h3921
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3922 | h3922
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3923 | h3923
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3924 | h3924
                      · linarith only [h0, h3888, h3894, h3924, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3926 | h3926
                        · linarith only [h0, h3889, h3924, h3926, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h3894, h3920, h3922, h3926, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h3892, h3923, hlam]
                  · linarith only [h0, h3891, h3922, hlam]
                · linarith only [h3894, h3920, h3921, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3932 | h3932
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3933 | h3933
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3934 | h3934
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3935 | h3935
                      · linarith only [h0, h3888, h3935, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3937 | h3937
                        · linarith only [h0, h3889, h3920, h3935, h3937, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3939 | h3939
                          · linarith only [h0, h3889, h3939, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h0, h3889, h3932, h3934, h3939, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h0, h3892, h3934, hlam]
                  · linarith only [h0, h3891, h3933, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3944 | h3944
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3945 | h3945
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h3946 | h3946
                      · linarith only [h0, h3888, h3946, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h3948 | h3948
                        · linarith only [h0, h3889, h3920, h3946, h3948, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h3950 | h3950
                          · linarith only [h0, h3889, h3932, h3950, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h3952 | h3952
                            · linarith only [h3888, h3894, h3944, h3952, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h3954 | h3954
                              · linarith only [h0, h3888, h3920, h3944, h3954, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h3956 | h3956
                                · linarith only [h0, h3892, h3894, h3932, h3956, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h3958 | h3958
                                  · rcases h0bigk with h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c | h3959c
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h0, hlam, p3959_1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h0, h3888, h3944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3959_1, u1elo1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h0, h3888, h3894, h3944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3959_1, u1elo1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h0, h3888, h3894, h3932, h3944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3959_1, u1elo1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p3959_1, u1elo1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      rcases p3959_3 (m.d 0 1) (by simp) with h3967 | h3967
                                      · linarith only [h0, h3967, hlam]
                                      · linarith only [h3888, h3967, hlam]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      rcases p3959_3 (m.d 0 1) (by simp) with h3970 | h3970
                                      · linarith only [h0, h3970, hlam]
                                      · linarith only [h3889, h3970, hlam]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      rcases p3959_3 (m.d 0 1) (by simp) with h3973 | h3973
                                      · linarith only [h0, h3973, hlam]
                                      · linarith only [h3890, h3973, hlam]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3888, hlam, p3959_1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3891, hlam, p3959_1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3894, hlam, p3959_1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3920, hlam, p3959_1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3889, hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3892, hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3888, h3932, h3944, h3958, hc23, hc34, hlam, hphi, p3959_1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3932, hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3890, hlam, p3959_0]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h3893, hlam, p3959_1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h0, h3888, h3890, h3944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3959_1, u1elo1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [h0, h3890, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3959_1, u1elo1]
                                    · have p3959_0 := h3959c.1
                                      have p3959_1 := h3959c.2.1
                                      have p3959_2 := h3959c.2.2.1
                                      have p3959_3 := h3959c.2.2.2
                                      linarith only [hlam, p3959_0]
                                  · rcases h0bigk with h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c | h3991c
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, hlam, p3991_1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, h3888, h3944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3991_1, u1elo1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, h3889, h3944, h3946, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3991_1, u1elo1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht5b, p3991_1, u1elo1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p3991_1, u1elo1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      rcases p3991_3 (m.d 0 1) (by simp) with h3999 | h3999
                                      · linarith only [h0, h3999, hlam]
                                      · linarith only [h3888, h3999, hlam]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      rcases p3991_3 (m.d 0 1) (by simp) with h4002 | h4002
                                      · linarith only [h0, h4002, hlam]
                                      · linarith only [h3889, h4002, hlam]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      rcases p3991_3 (m.d 0 1) (by simp) with h4005 | h4005
                                      · linarith only [h0, h4005, hlam]
                                      · linarith only [h3890, h4005, hlam]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3888, hlam, p3991_1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3891, hlam, p3991_1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3894, hlam, p3991_1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3920, hlam, p3991_1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3889, hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3892, hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, h3888, h3889, h3944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3991_1, u1elo1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3932, hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3890, hlam, p3991_0]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h3893, hlam, p3991_1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, h3888, h3890, h3944, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3991_1, u1elo1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [h0, h3890, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p3991_1, u1elo1]
                                    · have p3991_0 := h3991c.1
                                      have p3991_1 := h3991c.2.1
                                      have p3991_2 := h3991c.2.2.1
                                      have p3991_3 := h3991c.2.2.2
                                      linarith only [hlam, p3991_0]
                    · linarith only [h0, h3892, h3945, hlam]
                  · linarith only [h0, h3891, h3944, hlam]
          · linarith only [h0, h3890, h3893, hlam]
        · linarith only [h0, h3889, h3892, hlam]
      · linarith only [h0, h3888, h3891, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4028 | h4028
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4029 | h4029
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4030 | h4030
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4031 | h4031
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4032 | h4032
              · linarith only [h3888, h3890, h4032, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4034 | h4034
                · linarith only [h3888, h3890, h4031, h4034, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4036 | h4036
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4037 | h4037
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4038 | h4038
                      · linarith only [h0, h3888, h4038, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3888, h4031, h4038, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h4029, h4037, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h4028, h4036, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4043 | h4043
              · linarith only [h3888, h3890, h4043, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4045 | h4045
                · linarith only [h3889, h3890, h4045, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4047 | h4047
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4048 | h4048
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4049 | h4049
                      · linarith only [h3888, h4031, h4049, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4051 | h4051
                        · linarith only [h3888, h3890, h4043, h4051, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4053 | h4053
                          · linarith only [h3889, h3890, h4045, h4053, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4055 | h4055
                            · linarith only [h3888, h4028, h4031, h4055, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4057 | h4057
                              · linarith only [h3890, h4047, h4051, h4057, hc01, hlam, hphi, u1elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4059 | h4059
                                · linarith only [h3889, h3890, h4048, h4053, h4059, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4061 | h4061
                                  · linarith only [h3889, h3890, h4047, h4049, h4053, h4061, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [hlam, p4063_0]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h0, hlam, p4063_1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h0, h3888, h4047, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4063_1, u1elo1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h0, h3888, h4031, h4047, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4063_1, u1elo1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h3890, hlam, p4063_1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h3889, hc14, hlam, hphi, ht0b, ht45, ht5b, p4063_1, u0elo1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [hlam, p4063_0]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      rcases p4063_3 (m.d 0 1) (by simp) with h4071 | h4071
                                      · linarith only [h0, h4071, hlam]
                                      · linarith only [h3888, h4071, hlam]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      rcases p4063_3 (m.d 0 1) (by simp) with h4074 | h4074
                                      · linarith only [h0, h4074, hlam]
                                      · linarith only [h3889, h4074, hlam]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h0, h3889, h3890, h4047, h4049, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4063_1, u1elo1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h3888, hlam, p4063_1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h4028, hlam, p4063_1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [hlam, p4063_0]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h4031, hlam, p4063_1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h4043, hlam, p4063_1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h3889, hlam, p4063_0]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h4029, hlam, p4063_0]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h3888, h3889, h3890, h4047, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4063_1, u1elo4]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [hlam, p4063_0]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h4045, hlam, p4063_0]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h3888, h4047, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4063_1, u0elo4]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [h4030, hlam, p4063_1]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      rcases p4063_3 (m.d 0 1) (by simp) with h4090 | h4090
                                      · linarith only [h3890, h4090, hlam]
                                      · linarith only [h3888, h4090, hlam]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      rcases p4063_3 (m.d 0 1) (by simp) with h4093 | h4093
                                      · linarith only [h3890, h4093, hlam]
                                      · linarith only [h3889, h4093, hlam]
                                    · have p4063_0 := h4063c.1
                                      have p4063_1 := h4063c.2.1
                                      have p4063_2 := h4063c.2.2.1
                                      have p4063_3 := h4063c.2.2.2
                                      linarith only [hlam, p4063_0]
                    · linarith only [h0, h4029, h4048, hlam]
                  · linarith only [h0, h4028, h4047, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4099 | h4099
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4100 | h4100
              · linarith only [h0, h3888, h4030, h4100, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4102 | h4102
                · linarith only [h0, h3889, h4030, h4102, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4104 | h4104
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4105 | h4105
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4106 | h4106
                      · linarith only [h0, h3888, h4106, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h3888, h4099, h4106, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h4029, h4105, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h4028, h4104, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4111 | h4111
              · linarith only [h0, h3889, h4030, h4099, h4111, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4113 | h4113
                · linarith only [h0, h3889, h4030, h4113, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4115 | h4115
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4116 | h4116
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4117 | h4117
                      · linarith only [h3888, h4099, h4117, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4119 | h4119
                        · linarith only [h0, h3888, h4030, h4111, h4119, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4121 | h4121
                          · linarith only [h0, h3889, h4099, h4113, h4121, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4123 | h4123
                            · linarith only [h3888, h4099, h4115, h4123, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4125 | h4125
                              · linarith only [h3890, h4115, h4119, h4125, hc01, hlam, hphi, u1elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4127 | h4127
                                · linarith only [h3889, h3890, h4116, h4121, h4127, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4129 | h4129
                                  · linarith only [h0, h3889, h4030, h4115, h4117, h4127, h4129, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c | h4131c
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h0, hlam, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3890, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4131_1, u1elo4]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3890, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p4131_1, u1elo4]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3890, hlam, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3889, h4030, h4117, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4131_1, u0elo4]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3888, h4030, h4115, h4125, h4129, hc23, hc45, hlam, hphi, ht34, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3889, h4030, h4115, h4117, h4125, h4129, hc23, hc45, hlam, hphi, ht34, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h4030, hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3888, hlam, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h4028, hlam, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h4099, hlam, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h4111, hlam, p4131_1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3889, hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h4029, hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h0, h3888, h3889, h4115, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4131_1, u1elo1]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h4113, hlam, p4131_0]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h3890, hc01, hlam, hphi, p4131_1, u1elo4]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [h0, h3889, h3890, h4115, h4117, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4131_1, u1elo4]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      rcases p4131_3 (m.d 0 1) (by simp) with h4154 | h4154
                                      · linarith only [h3890, h4154, hlam]
                                      · linarith only [h3888, h4154, hlam]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      rcases p4131_3 (m.d 0 1) (by simp) with h4157 | h4157
                                      · linarith only [h3890, h4157, hlam]
                                      · linarith only [h3889, h4157, hlam]
                                    · have p4131_0 := h4131c.1
                                      have p4131_1 := h4131c.2.1
                                      have p4131_2 := h4131c.2.2.1
                                      have p4131_3 := h4131c.2.2.2
                                      linarith only [hlam, p4131_0]
                    · linarith only [h0, h4029, h4116, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h4028, h4115, hlam]
        · linarith only [h0, h3889, h4029, hlam]
      · linarith only [h0, h3888, h4028, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4165 | h4165
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4166 | h4166
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4167 | h4167
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4168 | h4168
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4169 | h4169
            · linarith only [h3888, h3889, h4169, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4171 | h4171
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4172 | h4172
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4173 | h4173
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4174 | h4174
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4175 | h4175
                      · linarith only [h3888, h4169, h4175, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4177 | h4177
                        · linarith only [h3888, h3889, h4174, h4177, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h3888, h3889, h4171, h4173, h4174, h4177, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · linarith only [h0, h4167, h4174, hlam]
                  · linarith only [h0, h4166, h4173, hlam]
                · linarith only [h3888, h3889, h4171, h4172, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4183 | h4183
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4184 | h4184
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4185 | h4185
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4186 | h4186
                      · linarith only [h3888, h4169, h4186, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4188 | h4188
                        · linarith only [h3888, h3889, h4168, h4171, h4185, h4188, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4190 | h4190
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4191 | h4191
                            · linarith only [h3889, h4184, h4186, h4191, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4193 | h4193
                              · linarith only [h3889, h4165, h4184, h4188, h4193, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4195 | h4195
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4196 | h4196
                                  · rcases h0bigk with h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c | h4197c
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [hlam, p4197_0]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h0, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h3889, h4185, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4197_1, u1elo1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h3889, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h3889, h4185, hc05, hlam, hphi, ht01, ht0b, ht5b, p4197_1, u1elo1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p4197_1, u1elo1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [hlam, p4197_0]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      rcases p4197_3 (m.d 0 1) (by simp) with h4205 | h4205
                                      · linarith only [h0, h4205, hlam]
                                      · linarith only [h3888, h4205, hlam]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h0, h3889, h4165, h4184, h4188, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4197_1, u1elo1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      rcases p4197_3 (m.d 0 1) (by simp) with h4209 | h4209
                                      · linarith only [h0, h4209, hlam]
                                      · linarith only [h4165, h4209, hlam]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h3888, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4166, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [hlam, p4197_0]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4169, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4171, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4165, h4184, h4188, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4197_1, u0elo3]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4167, hlam, p4197_0]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      rcases p4197_3 (m.d 0 1) (by simp) with h4219 | h4219
                                      · linarith only [h3889, h4219, hlam]
                                      · linarith only [h3888, h4219, hlam]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [hlam, p4197_0]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      rcases p4197_3 (m.d 0 1) (by simp) with h4223 | h4223
                                      · linarith only [h3889, h4223, hlam]
                                      · linarith only [h4165, h4223, hlam]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4165, hlam, p4197_0]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4168, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h0, h3888, h4165, h4184, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4197_1, u1elo1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [h4183, hlam, p4197_1]
                                    · have p4197_0 := h4197c.1
                                      have p4197_1 := h4197c.2.1
                                      have p4197_2 := h4197c.2.2.1
                                      have p4197_3 := h4197c.2.2.2
                                      linarith only [hlam, p4197_0]
                                  · linarith only [h3889, h4186, h4190, h4196, hc01, hlam, hphi, u1elo4]
                                · linarith only [h3889, h4165, h4190, h4195, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                          · linarith only [h3889, h4165, h4184, h4188, h4190, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h4167, h4185, hlam]
                  · linarith only [h0, h4166, h4184, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3889, h4165, h4183, hlam]
          · linarith only [h0, h4165, h4168, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4238 | h4238
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4239 | h4239
            · linarith only [h0, h3888, h4167, h4239, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4241 | h4241
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4242 | h4242
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4243 | h4243
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4244 | h4244
                    · linarith only [h0, h3888, h4167, h4243, h4244, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4246 | h4246
                      · linarith only [h3888, h4239, h4246, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4248 | h4248
                        · linarith only [h0, h3888, h4244, h4248, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h3888, h4241, h4244, h4248, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h4166, h4243, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h3888, h4167, h4241, h4242, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4253 | h4253
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4254 | h4254
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4255 | h4255
                    · linarith only [h0, h3888, h4167, h4254, h4255, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4257 | h4257
                      · linarith only [h3888, h4239, h4257, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4259 | h4259
                        · linarith only [h0, h3888, h4241, h4255, h4259, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4261 | h4261
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4262 | h4262
                            · linarith only [h0, h3889, h4166, h4255, h4257, h4262, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h4165, h4254, h4255, h4259, h4262, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h4165, h4254, h4255, h4259, h4261, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h4166, h4254, hlam]
                · linarith only [h0, h4165, h4167, h4253, hlam]
          · linarith only [h0, h4165, h4238, hlam]
      · linarith only [h0, h3888, h4166, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4270 | h4270
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4271 | h4271
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4272 | h4272
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4273 | h4273
            · linarith only [h3888, h3889, h4273, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4275 | h4275
              · linarith only [h3888, h4165, h4275, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4277 | h4277
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4278 | h4278
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4279 | h4279
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4280 | h4280
                      · linarith only [h3888, h3889, h4273, h4279, h4280, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4282 | h4282
                        · linarith only [h3888, h4165, h4275, h4282, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4284 | h4284
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4285 | h4285
                            · linarith only [h3888, h3889, h4165, h4278, h4280, h4285, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4287 | h4287
                              · linarith only [h3888, h4165, h4278, h4282, h4287, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4289 | h4289
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4290 | h4290
                                  · rcases h0bigk with h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c | h4291c
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [hlam, p4291_0]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h0, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4165, h4279, h4284, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4291_1, u1elo1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h3889, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4165, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h3888, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4291_1, u0elo1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [hlam, p4291_0]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      rcases p4291_3 (m.d 0 1) (by simp) with h4299 | h4299
                                      · linarith only [h0, h4299, hlam]
                                      · linarith only [h3888, h4299, hlam]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h0, h3888, h4165, h4277, h4278, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4291_1, u1elo1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h0, h3888, h4165, h4278, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4291_1, u1elo1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h3888, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4270, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [hlam, p4291_0]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4273, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4275, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h3888, h4278, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4291_1, u0elo3]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4271, hlam, p4291_0]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      rcases p4291_3 (m.d 0 1) (by simp) with h4311 | h4311
                                      · linarith only [h3889, h4311, hlam]
                                      · linarith only [h3888, h4311, hlam]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [hlam, p4291_0]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h3888, h4165, h4278, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4291_1, u0elo3]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h3888, h4278, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4291_1, u0elo4]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4272, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      rcases p4291_3 (m.d 0 1) (by simp) with h4318 | h4318
                                      · linarith only [h4165, h4318, hlam]
                                      · linarith only [h3888, h4318, hlam]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [h4277, hlam, p4291_1]
                                    · have p4291_0 := h4291c.1
                                      have p4291_1 := h4291c.2.1
                                      have p4291_2 := h4291c.2.2.1
                                      have p4291_3 := h4291c.2.2.2
                                      linarith only [hlam, p4291_0]
                                  · linarith only [h3888, h3889, h4278, h4280, h4289, h4290, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4324 | h4324
                                  · rcases h0bigk with h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c | h4325c
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [hlam, p4325_0]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h0, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h3888, h4165, h4278, h4284, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4325_1, u1elo3]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h3889, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h4165, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, p4325_1, u1elo1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [hlam, p4325_0]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      rcases p4325_3 (m.d 0 1) (by simp) with h4333 | h4333
                                      · linarith only [h0, h4333, hlam]
                                      · linarith only [h3888, h4333, hlam]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h0, h4277, h4289, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4325_1, u1elo1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h0, h3888, h4165, h4278, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4325_1, u1elo1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h3888, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h4270, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [hlam, p4325_0]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h4273, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h4275, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h3888, h4278, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4325_1, u0elo3]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h4271, hlam, p4325_0]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      rcases p4325_3 (m.d 0 1) (by simp) with h4345 | h4345
                                      · linarith only [h3889, h4345, hlam]
                                      · linarith only [h3888, h4345, hlam]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [hlam, p4325_0]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h3888, h3889, h4165, h4278, h4279, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4325_1, u1elo1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h3888, h4278, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4325_1, u0elo4]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h4272, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      rcases p4325_3 (m.d 0 1) (by simp) with h4352 | h4352
                                      · linarith only [h4165, h4352, hlam]
                                      · linarith only [h3888, h4352, hlam]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [h4277, hlam, p4325_1]
                                    · have p4325_0 := h4325c.1
                                      have p4325_1 := h4325c.2.1
                                      have p4325_2 := h4325c.2.2.1
                                      have p4325_3 := h4325c.2.2.2
                                      linarith only [hlam, p4325_0]
                                  · linarith only [h3888, h3889, h4278, h4280, h4324, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h3889, h4277, h4284, hlam]
                    · linarith only [h0, h4271, h4279, hlam]
                  · linarith only [h0, h4270, h4278, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4361 | h4361
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4362 | h4362
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4363 | h4363
                      · linarith only [h3888, h3889, h4363, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4365 | h4365
                        · linarith only [h3888, h3889, h4362, h4365, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4367 | h4367
                          · linarith only [h3889, h4277, h4362, h4367, hc01, hlam, hphi, u1elo1]
                          · linarith only [h3888, h3889, h4361, h4367, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3888, h4271, h4362, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h3888, h4270, h4361, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4372 | h4372
            · linarith only [h3888, h3889, h4372, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4374 | h4374
              · linarith only [h0, h3888, h4272, h4374, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4376 | h4376
                · linarith only [h4271, h4272, h4376, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4378 | h4378
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4379 | h4379
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4380 | h4380
                      · linarith only [h3888, h4372, h4380, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4382 | h4382
                        · linarith only [h0, h3888, h4272, h4374, h4382, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4384 | h4384
                          · linarith only [h3889, h4376, h4379, h4384, hc01, hlam, hphi, u1elo1]
                          · linarith only [h3888, h3889, h4378, h4384, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h3888, h4271, h4378, h4379, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h4270, h4378, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4389 | h4389
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4390 | h4390
            · linarith only [h0, h3888, h4271, h4390, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4392 | h4392
              · linarith only [h3888, h4165, h4392, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4394 | h4394
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4395 | h4395
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4396 | h4396
                    · linarith only [h4165, h4271, h4389, h4396, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4398 | h4398
                      · linarith only [h3888, h4390, h4398, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4400 | h4400
                        · linarith only [h0, h3888, h4392, h4396, h4400, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4402 | h4402
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4403 | h4403
                            · linarith only [h0, h4165, h4270, h4396, h4398, h4402, h4403, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h3888, h4395, h4396, h4403, hc23, hc34, hlam, hphi]
                          · linarith only [h3889, h4394, h4402, hlam]
                  · linarith only [h0, h4270, h4395, hlam]
                · linarith only [h4271, h4389, h4394, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4409 | h4409
            · linarith only [h0, h3888, h4271, h4409, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4411 | h4411
              · linarith only [h3888, h4165, h4411, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4413 | h4413
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4414 | h4414
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4415 | h4415
                    · linarith only [h0, h3888, h4271, h4414, h4415, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4417 | h4417
                      · linarith only [h3888, h4409, h4417, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4419 | h4419
                        · linarith only [h0, h3888, h4389, h4411, h4415, h4419, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4421 | h4421
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4422 | h4422
                            · linarith only [h0, h3888, h4414, h4415, h4417, h4422, hlam]
                            · linarith only [h0, h3888, h4414, h4415, h4422, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h3888, h4414, h4415, h4421, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h4270, h4414, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4427 | h4427
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4428 | h4428
                    · linarith only [h0, h3888, h4271, h4427, h4428, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4430 | h4430
                      · linarith only [h0, h3888, h4428, h4430, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4432 | h4432
                        · linarith only [h0, h3888, h4428, h4432, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4434 | h4434
                          · linarith only [h3888, h3889, h4413, h4427, h4434, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                          · linarith only [h3888, h3889, h4427, h4434, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h4270, h4427, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h3888, h4270, hlam]

set_option maxHeartbeats 12148000 in
set_option maxHeartbeats 12148000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3888 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4439 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h4440 | h4440
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4441 | h4441
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4442 | h4442
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4443 | h4443
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4444 | h4444
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4445 | h4445
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4446 | h4446
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4447 | h4447
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4448 | h4448
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4449 | h4449
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4450 | h4450
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4451 | h4451
                        · linarith only [h3888, h4439, h4451, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h3888, h4439, h4446, h4447, h4451, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h3888, h4441, h4445, h4450, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h3888, h4444, h4449, hlam]
                  · linarith only [h0, h4442, h4448, hlam]
                · linarith only [h0, h4441, h4447, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4458 | h4458
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4459 | h4459
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4460 | h4460
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4461 | h4461
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4462 | h4462
                        · linarith only [h4439, h4446, h4462, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4464 | h4464
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4465 | h4465
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4466 | h4466
                              · linarith only [h4439, h4446, h4459, h4466, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4468 | h4468
                                · linarith only [h4439, h4446, h4459, h4464, h4468, hlam]
                                · rcases h0bigk with h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h0, hlam, p4470_1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h3888, hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h3888, h4458, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p4470_1, u1elo1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h3888, h4439, h4446, h4458, h4459, h4464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4470_1, u1elo1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4440, hc15, hlam, hphi, ht0b, ht5b, p4470_1, u0elo1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h0, h3888, h4439, h4459, h4464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4470_1, u1elo1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    rcases p4470_3 (m.d 0 1) (by simp) with h4479 | h4479
                                    · linarith only [h0, h4479, hlam]
                                    · linarith only [h4439, h4479, hlam]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    rcases p4470_3 (m.d 0 1) (by simp) with h4482 | h4482
                                    · linarith only [h0, h4482, hlam]
                                    · linarith only [h4440, h4482, hlam]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4440, h4459, h4462, h4464, hc34, hlam, hphi, ht0b, ht45, ht5b, p4470_1, u0elo2]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4441, hlam, p4470_1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    rcases p4470_3 (m.d 0 1) (by simp) with h4488 | h4488
                                    · linarith only [h3888, h4488, hlam]
                                    · linarith only [h4439, h4488, hlam]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    rcases p4470_3 (m.d 0 1) (by simp) with h4491 | h4491
                                    · linarith only [h3888, h4491, hlam]
                                    · linarith only [h4440, h4491, hlam]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4439, hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4442, hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4444, hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4446, hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4440, hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4443, hlam, p4470_1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h4445, hlam, p4470_0]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [h0, h4439, h4440, h4459, h4464, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4470_1, u1elo1]
                                  · have p4470_0 := h4470c.1
                                    have p4470_1 := h4470c.2.1
                                    have p4470_2 := h4470c.2.2.1
                                    have p4470_3 := h4470c.2.2.2
                                    linarith only [hlam, p4470_0]
                            · linarith only [h3888, h4440, h4458, h4461, h4465, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h3888, h4439, h4458, h4460, h4464, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h3888, h4445, h4461, hlam]
                    · linarith only [h3888, h4444, h4460, hlam]
                  · linarith only [h0, h4442, h4459, hlam]
                · linarith only [h0, h4441, h4458, hlam]
            · linarith only [h3888, h4440, h4445, hlam]
          · linarith only [h3888, h4439, h4444, hlam]
        · linarith only [h0, h4440, h4443, hlam]
      · linarith only [h3888, h4439, h4441, h4442, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4514 | h4514
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4515 | h4515
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4516 | h4516
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4517 | h4517
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4518 | h4518
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4519 | h4519
                · linarith only [h4441, h4514, h4519, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4521 | h4521
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4522 | h4522
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4523 | h4523
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4524 | h4524
                        · linarith only [h0, h4439, h4519, h4524, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h4439, h4518, h4519, h4524, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h3888, h4517, h4523, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h3888, h4516, h4522, hlam]
                  · linarith only [h0, h3888, h4439, h4441, h4514, h4521, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4530 | h4530
                · linarith only [h0, h4439, h4441, h4530, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4532 | h4532
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4533 | h4533
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4534 | h4534
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4535 | h4535
                        · linarith only [h4439, h4518, h4535, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4537 | h4537
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4538 | h4538
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4539 | h4539
                              · linarith only [h0, h4439, h4515, h4518, h4530, h4532, h4539, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4541 | h4541
                                · linarith only [h4439, h4518, h4532, h4537, h4541, hlam]
                                · rcases h0bigk with h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c | h4543c
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h0, hlam, p4543_1]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h3888, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h0, h4439, h4530, h4532, h4537, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4543_1]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h0, h4439, h4518, h4530, h4532, h4537, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4543_1]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h0, h4530, hc01, hc23, hlam, hphi, ht12, p4543_1]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4441, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    rcases p4543_3 (m.d 0 1) (by simp) with h4552 | h4552
                                    · linarith only [h0, h4552, hlam]
                                    · linarith only [h4439, h4552, hlam]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    rcases p4543_3 (m.d 0 1) (by simp) with h4555 | h4555
                                    · linarith only [h0, h4555, hlam]
                                    · linarith only [h4440, h4555, hlam]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h3888, h4440, h4532, h4535, h4537, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4543_1, u1elo2]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h0, h3888, h4440, h4532, h4535, h4537, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4543_1, u1elo2]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    rcases p4543_3 (m.d 0 1) (by simp) with h4561 | h4561
                                    · linarith only [h3888, h4561, hlam]
                                    · linarith only [h4439, h4561, hlam]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    rcases p4543_3 (m.d 0 1) (by simp) with h4564 | h4564
                                    · linarith only [h3888, h4564, hlam]
                                    · linarith only [h4440, h4564, hlam]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4439, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4514, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4516, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4518, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4440, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4515, hlam, p4543_1]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h4517, hlam, p4543_0]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [h0, h4439, h4440, h4530, h4532, h4537, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4543_1]
                                  · have p4543_0 := h4543c.1
                                    have p4543_1 := h4543c.2.1
                                    have p4543_2 := h4543c.2.2.1
                                    have p4543_3 := h4543c.2.2.2
                                    linarith only [hlam, p4543_0]
                            · linarith only [h0, h4530, h4538, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h4440, h4530, h4532, h4535, h4537, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h3888, h4517, h4534, hlam]
                    · linarith only [h3888, h4516, h4533, hlam]
                  · linarith only [h0, h4514, h4532, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h4440, h4441, h4517, hlam]
          · linarith only [h0, h4439, h4441, h4516, hlam]
        · linarith only [h0, h4440, h4515, hlam]
      · linarith only [h0, h4439, h4514, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4586 | h4586
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4587 | h4587
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4588 | h4588
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4589 | h4589
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4590 | h4590
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4591 | h4591
              · linarith only [h4439, h4440, h4591, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4593 | h4593
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4594 | h4594
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4595 | h4595
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4596 | h4596
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4597 | h4597
                        · linarith only [h4439, h4591, h4597, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4599 | h4599
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4600 | h4600
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4601 | h4601
                              · linarith only [h0, h4440, h4587, h4597, h4601, hc01, hlam, hphi, u1elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4603 | h4603
                                · linarith only [h4439, h4440, h4594, h4597, h4599, h4603, hlam]
                                · rcases h0bigk with h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c | h4605c
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h0, hlam, p4605_1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h3888, hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4439, h4440, h4594, h4599, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4605_1, u1elo4]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4440, hlam, p4605_1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, p4605_1, u1elo1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h0, h3888, hc01, hlam, hphi, p4605_1, u1elo1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    rcases p4605_3 (m.d 0 1) (by simp) with h4614 | h4614
                                    · linarith only [h0, h4614, hlam]
                                    · linarith only [h4439, h4614, hlam]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h0, h4439, h4440, h4594, h4599, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4605_1, u1elo1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h3888, h4439, h4593, h4594, h4599, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4605_1, u1elo1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4586, hlam, p4605_1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    rcases p4605_3 (m.d 0 1) (by simp) with h4621 | h4621
                                    · linarith only [h3888, h4621, hlam]
                                    · linarith only [h4439, h4621, hlam]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h3888, h4439, h4440, h4593, h4594, h4599, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4605_1, u1elo1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4439, hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4587, hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4589, hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4591, hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4439, h4594, h4599, hc34, hlam, hphi, ht0b, ht45, ht5b, p4605_1, u0elo4]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4588, hlam, p4605_1]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [h4590, hlam, p4605_0]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    rcases p4605_3 (m.d 0 1) (by simp) with h4633 | h4633
                                    · linarith only [h4440, h4633, hlam]
                                    · linarith only [h4439, h4633, hlam]
                                  · have p4605_0 := h4605c.1
                                    have p4605_1 := h4605c.2.1
                                    have p4605_2 := h4605c.2.2.1
                                    have p4605_3 := h4605c.2.2.2
                                    linarith only [hlam, p4605_0]
                            · linarith only [h3888, h4590, h4593, h4599, h4600, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h4439, h4440, h4593, h4595, h4596, h4599, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h3888, h4590, h4596, hlam]
                    · linarith only [h3888, h4589, h4595, hlam]
                  · linarith only [h0, h4587, h4594, hlam]
                · linarith only [h0, h4586, h4593, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4643 | h4643
              · linarith only [h3888, h4439, h4590, h4643, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4645 | h4645
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4646 | h4646
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4647 | h4647
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4648 | h4648
                      · linarith only [h3888, h4590, h4648, hc01, hlam, hphi, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4650 | h4650
                        · linarith only [h4439, h4643, h4650, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4652 | h4652
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4653 | h4653
                            · linarith only [h3888, h4586, h4648, h4653, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4655 | h4655
                              · linarith only [h3888, h4439, h4646, h4648, h4650, h4655, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4657 | h4657
                                · linarith only [h3888, h4439, h4646, h4648, h4650, h4652, h4657, hlam]
                                · linarith only [h3888, h4439, h4646, h4648, h4652, h4657, hc34, hc45, hlam, hphi]
                          · linarith only [h3888, h4589, h4648, h4652, hc23, hc35, hlam, hphi]
                    · linarith only [h3888, h4439, h4589, h4647, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h4587, h4646, hlam]
                · linarith only [h0, h4586, h4645, hlam]
          · linarith only [h3888, h4439, h4589, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4665 | h4665
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4666 | h4666
            · linarith only [h4586, h4588, h4666, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4668 | h4668
              · linarith only [h3888, h4439, h4586, h4588, h4668, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4670 | h4670
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4671 | h4671
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4672 | h4672
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4673 | h4673
                      · linarith only [h3888, h4439, h4666, h4671, h4673, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4675 | h4675
                        · linarith only [h4439, h4668, h4675, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4677 | h4677
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4678 | h4678
                            · linarith only [h3888, h4440, h4586, h4588, h4673, h4678, hc01, hlam, hphi, u1elo4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4680 | h4680
                              · linarith only [h3888, h4439, h4440, h4671, h4675, h4680, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                              · linarith only [h4586, h4588, h4677, h4680, hc34, hc45, hlam, hphi]
                          · linarith only [h3888, h4665, h4673, h4677, hc23, hc35, hlam, hphi]
                    · linarith only [h3888, h4439, h4665, h4671, h4672, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h4587, h4588, h4671, hc12, hc25, hlam, hphi]
                · linarith only [h0, h4586, h4670, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h3888, h4439, h4665, hlam]
      · linarith only [h3888, h4439, h4586, h4587, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4689 | h4689
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4690 | h4690
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4691 | h4691
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4692 | h4692
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4693 | h4693
              · linarith only [h4439, h4440, h4693, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4695 | h4695
                · linarith only [h4586, h4689, h4695, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4697 | h4697
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4698 | h4698
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4699 | h4699
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4700 | h4700
                        · linarith only [h0, h4439, h4693, h4695, h4700, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4702 | h4702
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4703 | h4703
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4704 | h4704
                              · linarith only [h4440, h4689, h4700, h4704, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4706 | h4706
                                · linarith only [h4439, h4440, h4697, h4700, h4702, h4706, hlam]
                                · rcases h0bigk with h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c | h4708c
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h0, hlam, p4708_1]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h3888, hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4440, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p4708_1, u1elo4]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4440, hlam, p4708_1]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h0, h4695, hc01, hc23, hlam, hphi, ht12, p4708_1]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4586, hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    rcases p4708_3 (m.d 0 1) (by simp) with h4717 | h4717
                                    · linarith only [h0, h4717, hlam]
                                    · linarith only [h4439, h4717, hlam]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h0, h4439, h4440, h4695, h4697, h4702, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4708_1]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h3888, h4439, h4697, h4702, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4708_1, u1elo2]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h0, h3888, h4439, h4697, h4702, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4708_1, u1elo2]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    rcases p4708_3 (m.d 0 1) (by simp) with h4724 | h4724
                                    · linarith only [h3888, h4724, hlam]
                                    · linarith only [h4439, h4724, hlam]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h3888, h4439, h4440, h4697, h4702, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4708_1, u1elo2]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4439, hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4689, hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4691, hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4693, hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4439, h4697, h4702, hc34, hlam, hphi, ht0b, ht45, ht5b, p4708_1, u0elo4]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4690, hlam, p4708_1]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [h4692, hlam, p4708_0]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    rcases p4708_3 (m.d 0 1) (by simp) with h4736 | h4736
                                    · linarith only [h4440, h4736, hlam]
                                    · linarith only [h4439, h4736, hlam]
                                  · have p4708_0 := h4708c.1
                                    have p4708_1 := h4708c.2.1
                                    have p4708_2 := h4708c.2.2.1
                                    have p4708_3 := h4708c.2.2.2
                                    linarith only [hlam, p4708_0]
                            · linarith only [h0, h4439, h4695, h4697, h4702, h4703, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h4695, h4702, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h3888, h4439, h4690, h4692, h4699, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h3888, h4691, h4698, hlam]
                  · linarith only [h0, h3888, h4586, h4689, h4697, hc01, hlam, hphi, u1elo2]
            · linarith only [h4586, h4690, h4692, hlam]
          · linarith only [h0, h4439, h4586, h4691, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4747 | h4747
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4748 | h4748
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4749 | h4749
              · linarith only [h0, h4439, h4690, h4749, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4751 | h4751
                · linarith only [h0, h4586, h4751, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4753 | h4753
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4754 | h4754
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4755 | h4755
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4756 | h4756
                        · linarith only [h4439, h4749, h4756, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4758 | h4758
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4759 | h4759
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4760 | h4760
                              · linarith only [h4439, h4440, h4753, h4756, h4760, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4762 | h4762
                                · linarith only [h0, h4439, h4690, h4751, h4753, h4758, h4760, h4762, hc02, hc23, hlam, hphi]
                                · rcases h0bigk with h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c | h4764c
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h0, hlam, p4764_1]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h3888, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h0, h4439, h4751, h4753, h4758, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4764_1]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4440, hlam, p4764_1]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4690, hc01, hc25, hlam, hphi, ht12, p4764_1]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4586, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4439, h4690, h4753, h4758, h4760, hc34, hc45, hlam, hphi, p4764_1]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4690, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h3888, h4439, h4753, h4758, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4764_1, u1elo2]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h0, h3888, h4439, h4753, h4758, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4764_1, u1elo2]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    rcases p4764_3 (m.d 0 1) (by simp) with h4778 | h4778
                                    · linarith only [h3888, h4778, hlam]
                                    · linarith only [h4439, h4778, hlam]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h3888, h4439, h4440, h4753, h4758, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4764_1, u1elo2]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4439, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4689, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4747, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4749, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4439, h4753, h4758, hc34, hlam, hphi, ht0b, ht45, ht5b, p4764_1, u0elo4]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h0, h4439, h4440, h4753, h4758, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4764_1, u1elo4]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [h4748, hlam, p4764_0]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    rcases p4764_3 (m.d 0 1) (by simp) with h4790 | h4790
                                    · linarith only [h4440, h4790, hlam]
                                    · linarith only [h4439, h4790, hlam]
                                  · have p4764_0 := h4764c.1
                                    have p4764_1 := h4764c.2.1
                                    have p4764_2 := h4764c.2.2.1
                                    have p4764_3 := h4764c.2.2.2
                                    linarith only [hlam, p4764_0]
                            · linarith only [h0, h3888, h4439, h4748, h4751, h4753, h4758, h4759, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h0, h4439, h4751, h4753, h4758, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h3888, h4748, h4755, hlam]
                    · linarith only [h3888, h4747, h4754, hlam]
                  · linarith only [h0, h4689, h4753, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4799 | h4799
              · linarith only [h0, h4439, h4586, h4748, h4799, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4801 | h4801
                · linarith only [h0, h4586, h4801, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4803 | h4803
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4804 | h4804
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4805 | h4805
                      · linarith only [h0, h4439, h4586, h4748, h4803, h4805, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4807 | h4807
                        · linarith only [h4439, h4799, h4807, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4809 | h4809
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4810 | h4810
                            · linarith only [h0, h4801, h4805, h4810, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h0, h4439, h4801, h4803, h4809, h4810, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h4801, h4809, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h4439, h4747, h4801, h4803, h4804, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h4439, h4689, h4803, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
          · linarith only [h0, h4439, h4586, h4747, hlam]
      · linarith only [h0, h4439, h4689, hlam]

end R2N4
