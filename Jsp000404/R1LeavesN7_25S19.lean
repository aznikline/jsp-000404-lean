import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5416000 in
set_option maxHeartbeats 5416000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3095 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3633 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3927 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3928 | h3928
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3929 | h3929
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3930 | h3930
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3931 | h3931
        · rcases m.htr 0 3 5 (by decide) (by decide) with h3932 | h3932
          · rcases m.htr 0 4 5 (by decide) (by decide) with h3933 | h3933
            · rcases m.htr 1 2 3 (by decide) (by decide) with h3934 | h3934
              · rcases m.htr 1 2 4 (by decide) (by decide) with h3935 | h3935
                · rcases m.htr 1 2 5 (by decide) (by decide) with h3936 | h3936
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h3937 | h3937
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3938 | h3938
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3939 | h3939
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3940 | h3940
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3941 | h3941
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3942 | h3942
                              · rcases h0bigk with h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c | h3943c
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h0, hlam, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3095, hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3633, hlam, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3633, h3934, h3937, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h0, h3928, h3939, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h0, h3633, h3927, h3936, h3940, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  rcases p3943_3 (m.d 0 1) (by simp) with h3953 | h3953
                                  · linarith only [h0, h3953, hlam]
                                  · linarith only [h3927, h3953, hlam]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3927, h3936, h3940, h3942, hc03, hc45, hlam, hphi, ht0b, ht5b, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3928, hlam, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3095, h3633, h3927, h3934, h3936, h3940, h3942, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  rcases p3943_3 (m.d 0 1) (by simp) with h3960 | h3960
                                  · linarith only [h3095, h3960, hlam]
                                  · linarith only [h3927, h3960, hlam]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3927, h3936, h3940, h3942, hc04, hc45, hlam, hphi, ht0b, ht5b, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3929, hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3931, hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  rcases p3943_3 (m.d 0 1) (by simp) with h3967 | h3967
                                  · linarith only [h3633, h3967, hlam]
                                  · linarith only [h3927, h3967, hlam]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3927, hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3930, hlam, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3932, hlam, p3943_0]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [h3933, hlam, p3943_1]
                                · have p3943_0 := h3943c.1
                                  have p3943_1 := h3943c.2.1
                                  have p3943_2 := h3943c.2.2.1
                                  have p3943_3 := h3943c.2.2.2
                                  linarith only [hlam, p3943_0]
                              · rcases h0bigk with h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h0, hlam, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3095, hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3633, hlam, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3927, h3936, h3941, h3942, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h0, h3095, h3927, h3936, h3941, h3942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h0, h3633, h3927, h3936, h3941, h3942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h0, h3927, h3936, h3941, h3942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3927, h3936, h3941, h3942, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3928, hlam, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3095, h3633, h3927, h3934, h3936, h3941, h3942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3095, h3927, h3934, h3936, h3941, h3942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3927, h3936, h3941, h3942, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3929, hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3931, hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3633, h3927, h3934, h3936, h3937, h3941, h3942, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3927, hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3930, hlam, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3932, hlam, p3975_0]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [h3933, hlam, p3975_1]
                                · have p3975_0 := h3975c.1
                                  have p3975_1 := h3975c.2.1
                                  have p3975_2 := h3975c.2.2.1
                                  have p3975_3 := h3975c.2.2.2
                                  linarith only [hlam, p3975_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4001 | h4001
                              · linarith only [h3939, h3941, h4001, hlam]
                              · rcases h0bigk with h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c | h4003c
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3095, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3633, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, h3095, h3927, h3938, h3939, h3941, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, h3633, h3927, h3938, h3939, h3941, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h0, h3927, h3938, h3939, h3941, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3927, h3938, h3939, h3941, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3928, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3095, h3633, h3927, h3934, h3938, h3939, h3941, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3095, h3927, h3934, h3938, h3939, h3941, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3927, h3938, h3939, h3941, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3929, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3931, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3927, h3938, h3939, h3941, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3927, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3930, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3932, hlam, p4003_0]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [h3933, hlam, p4003_1]
                                · have p4003_0 := h4003c.1
                                  have p4003_1 := h4003c.2.1
                                  have p4003_2 := h4003c.2.2.1
                                  have p4003_3 := h4003c.2.2.2
                                  linarith only [hlam, p4003_0]
                          · linarith only [h3932, h3939, h3940, hc34, hlam, hphi, ht45, u5elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4030 | h4030
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4031 | h4031
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4032 | h4032
                              · rcases h0bigk with h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c | h4033c
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h0, hlam, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3095, hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3633, hlam, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3633, h3934, h3937, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h0, h3095, h3927, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h0, h3633, h3927, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  rcases p4033_3 (m.d 0 1) (by simp) with h4043 | h4043
                                  · linarith only [h0, h4043, hlam]
                                  · linarith only [h3927, h4043, hlam]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3927, h3936, h4030, h4032, hc03, hc45, hlam, hphi, ht0b, ht5b, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3928, hlam, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3095, h3931, h3934, h3939, h4030, h4032, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  rcases p4033_3 (m.d 0 1) (by simp) with h4050 | h4050
                                  · linarith only [h3095, h4050, hlam]
                                  · linarith only [h3927, h4050, hlam]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3927, h3936, h4030, h4032, hc04, hc45, hlam, hphi, ht0b, ht5b, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3929, hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3931, hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  rcases p4033_3 (m.d 0 1) (by simp) with h4057 | h4057
                                  · linarith only [h3633, h4057, hlam]
                                  · linarith only [h3927, h4057, hlam]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3927, hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3930, hlam, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3932, hlam, p4033_0]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [h3933, hlam, p4033_1]
                                · have p4033_0 := h4033c.1
                                  have p4033_1 := h4033c.2.1
                                  have p4033_2 := h4033c.2.2.1
                                  have p4033_3 := h4033c.2.2.2
                                  linarith only [hlam, p4033_0]
                              · linarith only [h3939, h4030, h4032, hc35, hlam, hphi, u5elo4]
                            · linarith only [h3927, h3938, h3939, h4030, h4031, hc35, hlam, hphi, u5elo0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4067 | h4067
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4068 | h4068
                              · rcases h0bigk with h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c | h4069c
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h0, hlam, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3095, hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3633, hlam, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3633, h3934, h3937, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h0, h3931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h0, h3633, h3927, h3932, h4030, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h0, h3932, h4030, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3927, h3932, h4030, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3928, hlam, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3095, h3633, h3927, h3932, h3934, h4030, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3095, h3932, h3934, h4030, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3927, h3932, h4030, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3929, hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3931, hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3633, h3932, h3934, h3937, h4030, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3927, hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3930, hlam, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3932, hlam, p4069_0]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [h3933, hlam, p4069_1]
                                · have p4069_0 := h4069c.1
                                  have p4069_1 := h4069c.2.1
                                  have p4069_2 := h4069c.2.2.1
                                  have p4069_3 := h4069c.2.2.2
                                  linarith only [hlam, p4069_0]
                              · linarith only [h3939, h4068, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4096 | h4096
                              · rcases h0bigk with h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h0, hlam, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3095, hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3633, hlam, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3927, h3938, h3939, h4067, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h0, h3931, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h0, h3633, h3927, h3938, h3939, h4067, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h0, h3927, h3938, h3939, h4067, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3927, h3938, h3939, h4067, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3928, hlam, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3095, h3633, h3927, h3934, h3938, h3939, h4067, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3095, h3927, h3934, h3938, h3939, h4067, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3927, h3938, h3939, h4067, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3929, hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3931, hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3633, h3927, h3934, h3937, h3938, h3939, h4067, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3927, hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3930, hlam, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3932, hlam, p4097_0]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [h3933, hlam, p4097_1]
                                · have p4097_0 := h4097c.1
                                  have p4097_1 := h4097c.2.1
                                  have p4097_2 := h4097c.2.2.1
                                  have p4097_3 := h4097c.2.2.2
                                  linarith only [hlam, p4097_0]
                              · linarith only [h3927, h3938, h3939, h4096, hc23, hlam, hphi, ht34, ht45, u5elo0]
                      · linarith only [h3633, h3933, h3938, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                    · linarith only [h3095, h3931, h3937, hlam]
                  · linarith only [h3095, h3934, h3936, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h3095, h3927, h3929, h3934, h3935, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h3928, h3934, hlam]
            · linarith only [h3633, h3927, h3933, hc15, hlam, hphi, u5elo4]
          · linarith only [h3931, h3932, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4131 | h4131
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4132 | h4132
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4133 | h4133
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4134 | h4134
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4135 | h4135
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4136 | h4136
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4137 | h4137
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4138 | h4138
                        · linarith only [h3095, h3927, h3928, h3931, h4135, h4138, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4140 | h4140
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4141 | h4141
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4142 | h4142
                              · rcases h0bigk with h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h0, hlam, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3095, hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3633, hlam, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3095, h3931, h4136, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h0, h3095, h3927, h4135, h4140, h4142, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h0, h3095, h3927, h3931, h4135, h4140, h4142, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  rcases p4143_3 (m.d 0 1) (by simp) with h4153 | h4153
                                  · linarith only [h0, h4153, hlam]
                                  · linarith only [h3927, h4153, hlam]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3927, h4135, h4140, h4142, hc03, hc45, hlam, hphi, ht0b, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3928, hlam, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3931, hlam, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3927, h3931, h4133, h4135, h4136, h4140, h4142, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3927, h3931, h4133, h4135, h4136, h4140, h4142, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3929, hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3931, h4133, h4136, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3927, h3931, h4133, h4135, h4136, h4140, h4142, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3927, hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h3930, hlam, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h4131, hlam, p4143_0]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [h4132, hlam, p4143_1]
                                · have p4143_0 := h4143c.1
                                  have p4143_1 := h4143c.2.1
                                  have p4143_2 := h4143c.2.2.1
                                  have p4143_3 := h4143c.2.2.2
                                  linarith only [hlam, p4143_0]
                              · linarith only [h3633, h3927, h3931, h4135, h4142, hc25, hlam, hphi, u5elo4]
                            · linarith only [h3095, h3927, h3931, h4133, h4136, h4137, h4141, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h3931, h4131, h4133, h4136, h4140, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3095, h3931, h4136, h4137, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4175 | h4175
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4176 | h4176
                        · linarith only [h3095, h3927, h4135, h4136, h4176, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4178 | h4178
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4179 | h4179
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4180 | h4180
                              · rcases h0bigk with h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c | h4181c
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h0, hlam, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3095, hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3633, hlam, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3095, h3927, h4135, h4178, h4180, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h0, h3095, h3927, h4135, h4178, h4180, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h0, h3095, h3927, h3931, h4135, h4178, h4180, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  rcases p4181_3 (m.d 0 1) (by simp) with h4191 | h4191
                                  · linarith only [h0, h4191, hlam]
                                  · linarith only [h3927, h4191, hlam]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3927, h4135, h4178, h4180, hc03, hc45, hlam, hphi, ht0b, ht5b, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3928, hlam, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3931, hlam, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3095, h3927, h4135, h4136, h4178, h4180, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3633, h3927, h4135, h4136, h4178, h4180, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3929, hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3633, h4136, hc03, hc34, hlam, hphi, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  rcases p4181_3 (m.d 0 1) (by simp) with h4203 | h4203
                                  · linarith only [h3633, h4203, hlam]
                                  · linarith only [h3927, h4203, hlam]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3927, hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h3930, hlam, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h4131, hlam, p4181_0]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [h4132, hlam, p4181_1]
                                · have p4181_0 := h4181c.1
                                  have p4181_1 := h4181c.2.1
                                  have p4181_2 := h4181c.2.2.1
                                  have p4181_3 := h4181c.2.2.2
                                  linarith only [hlam, p4181_0]
                              · linarith only [h4136, h4180, hc13, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h3095, h3927, h4136, h4175, h4179, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h3095, h4131, h4136, h4178, hc23, hc34, hlam, hphi]
                      · linarith only [h3633, h4175, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h3927, h4135, hc15, hlam, hphi, u5elo2]
                · linarith only [h0, h3929, h4134, hlam]
              · linarith only [h0, h3928, h4133, hlam]
            · linarith only [h3095, h3927, h3931, h4132, hc15, hlam, hphi, u5elo4]
          · linarith only [h3095, h3927, h4131, hc15, hlam, hphi, u5elo3]
      · linarith only [h3929, h3930, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4221 | h4221
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4222 | h4222
        · linarith only [h3928, h3929, h4222, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4224 | h4224
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4225 | h4225
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4226 | h4226
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4227 | h4227
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4228 | h4228
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4229 | h4229
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4230 | h4230
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4231 | h4231
                        · linarith only [h3095, h3927, h3928, h4222, h4228, h4231, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4233 | h4233
                          · linarith only [h3928, h3929, h4226, h4229, h4231, h4233, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3928, h3929, h4224, h4226, h4229, h4231, h4233, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3633, h3927, h4228, h4230, hc25, hlam, hphi, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4237 | h4237
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4238 | h4238
                        · linarith only [h3928, h3929, h4227, h4229, h4238, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4240 | h4240
                          · linarith only [h3928, h3929, h4227, h4240, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h3928, h3929, h4224, h4227, h4240, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3633, h3927, h4228, h4237, hc25, hlam, hphi, u5elo4]
                  · linarith only [h3929, h4227, h4228, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4245 | h4245
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4246 | h4246
                    · linarith only [h3095, h3927, h4222, h4226, h4227, h4245, h4246, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4248 | h4248
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4249 | h4249
                        · linarith only [h0, h3928, h4227, h4246, h4249, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4251 | h4251
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4252 | h4252
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4253 | h4253
                              · rcases h0bigk with h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [hlam, p4254_0]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h0, hlam, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3095, hlam, p4254_0]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3633, hlam, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3095, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [hlam, p4254_0]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h0, h3095, h3927, h4227, h4245, h4249, h4251, h4253, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3929, hlam, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h0, h3927, h4227, h4245, h4249, h4251, h4253, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3927, h4245, h4251, h4253, hc03, hc45, hlam, hphi, ht0b, ht5b, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3928, hlam, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [hlam, p4254_0]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h4222, hlam, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h0, h3927, h3928, h4227, h4245, h4249, h4251, h4253, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3927, h4245, h4251, h4253, hc04, hc45, hlam, hphi, ht0b, ht5b, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3929, h4249, hc02, hc34, hlam, hphi, ht23, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3929, h4249, hc03, hc34, hlam, hphi, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [hlam, p4254_0]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  rcases p4254_3 (m.d 0 1) (by simp) with h4274 | h4274
                                  · linarith only [h3633, h4274, hlam]
                                  · linarith only [h3927, h4274, hlam]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h3927, hlam, p4254_0]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h4221, hlam, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h4224, hlam, p4254_0]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [h4225, hlam, p4254_1]
                                · have p4254_0 := h4254c.1
                                  have p4254_1 := h4254c.2.1
                                  have p4254_2 := h4254c.2.2.1
                                  have p4254_3 := h4254c.2.2.2
                                  linarith only [hlam, p4254_0]
                              · linarith only [h4227, h4249, h4253, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                            · linarith only [h3095, h3927, h4226, h4227, h4248, h4252, hlam]
                          · linarith only [h3095, h4224, h4226, h4227, h4249, h4251, hc23, hc34, hlam, hphi]
                      · linarith only [h3633, h3927, h4245, h4248, hc25, hlam, hphi, u5elo4]
                  · linarith only [h0, h4245, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h3927, h3928, h4226, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h3633, h3927, h4225, hc15, hlam, hphi, u5elo4]
          · linarith only [h3095, h3927, h4224, hc15, hlam, hphi, u5elo3]
      · linarith only [h0, h3927, h4221, hc15, hlam, hphi, u5elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4291 | h4291
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4292 | h4292
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4293 | h4293
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4294 | h4294
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4295 | h4295
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4296 | h4296
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4297 | h4297
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4298 | h4298
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4299 | h4299
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4300 | h4300
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4301 | h4301
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4302 | h4302
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4303 | h4303
                            · linarith only [h3928, h4291, h4296, h4303, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h3928, h4291, h4295, h4296, h4303, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h3928, h4302, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h3633, h3927, h3928, h4291, h4293, h4298, h4301, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h3633, h3927, h4298, h4300, hc25, hlam, hphi, u5elo4]
                    · linarith only [h3928, h4291, h4293, h4296, h4299, hlam]
                  · linarith only [h3633, h3927, h3928, h4291, h4296, h4298, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h3928, h4291, h4296, h4297, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4312 | h4312
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4313 | h4313
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4314 | h4314
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4315 | h4315
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4316 | h4316
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4317 | h4317
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4318 | h4318
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4319 | h4319
                              · rcases h0bigk with h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c | h4320c
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h0, hlam, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3095, hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3633, hlam, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3633, h3927, h4312, h4313, h4317, h4319, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h0, h4296, hc01, hc23, hlam, hphi, ht12, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3928, hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h0, h3633, h3927, h4296, h4313, h4317, h4319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h0, h3927, h4296, h4313, h4317, h4319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3927, h3928, h4313, h4317, h4319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3928, hc02, hc23, hlam, hphi, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3633, h3927, h3928, h4313, h4317, h4319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  rcases p4320_3 (m.d 0 1) (by simp) with h4335 | h4335
                                  · linarith only [h3095, h4335, hlam]
                                  · linarith only [h3927, h4335, hlam]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3927, h4313, h4317, h4319, hc04, hc45, hlam, hphi, ht0b, ht5b, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h4291, hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h4293, hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3633, h3927, h4296, h4312, h4313, h4317, h4319, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h3927, hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h4292, hlam, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h4294, hlam, p4320_0]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [h4295, hlam, p4320_1]
                                · have p4320_0 := h4320c.1
                                  have p4320_1 := h4320c.2.1
                                  have p4320_2 := h4320c.2.2.1
                                  have p4320_3 := h4320c.2.2.2
                                  linarith only [hlam, p4320_0]
                              · linarith only [h0, h3927, h4296, h4315, h4319, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h3633, h3927, h4296, h4312, h4315, h4318, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h3633, h4296, h4312, h4317, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h3633, h3927, h4296, h4312, h4315, h4316, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h3633, h3927, h4315, hc15, hlam, hphi, u5elo4]
                    · linarith only [h3095, h3633, h3927, h4293, h4296, h4312, h4313, h4314, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h3633, h4312, h4313, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
                · linarith only [h0, h3927, h4291, h4312, hc02, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h3633, h3927, h4295, hc15, hlam, hphi, u5elo4]
          · linarith only [h3095, h3927, h4294, hc15, hlam, hphi, u5elo3]
        · linarith only [h3928, h4291, h4293, hlam]
      · linarith only [h4291, h4292, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4360 | h4360
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4361 | h4361
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4362 | h4362
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4363 | h4363
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4364 | h4364
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4365 | h4365
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4366 | h4366
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4367 | h4367
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4368 | h4368
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4369 | h4369
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4370 | h4370
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4371 | h4371
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4372 | h4372
                              · rcases h0bigk with h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c | h4373c
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h0, hlam, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3095, hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3633, hlam, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h0, h3927, h4291, h4364, h4366, h4369, h4370, h4372, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h4291, h4364, h4369, hc01, hc12, hlam, hphi, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3928, hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h4291, hlam, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3927, h4291, h4364, h4366, h4369, h4370, h4372, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3927, h4366, h4370, h4372, hc03, hc45, hlam, hphi, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3928, h4364, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h0, h3927, h3928, h4291, h4364, h4366, h4370, h4372, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3927, h3928, h4364, h4366, h4370, h4372, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3927, h4366, h4370, h4372, hc04, hc45, hlam, hphi, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h0, h3927, h4291, h4364, h4366, h4369, h4370, h4372, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h4361, hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3927, h4291, h4364, h4366, h4369, h4370, h4372, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h3927, hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h4360, hlam, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h4362, hlam, p4373_0]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [h4363, hlam, p4373_1]
                                · have p4373_0 := h4373c.1
                                  have p4373_1 := h4373c.2.1
                                  have p4373_2 := h4373c.2.2.1
                                  have p4373_3 := h4373c.2.2.2
                                  linarith only [hlam, p4373_0]
                              · linarith only [h0, h3927, h3928, h4364, h4368, h4372, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h3927, h4291, h4368, h4371, hlam]
                          · linarith only [h0, h4291, h4369, h4370, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                        · linarith only [h3928, h4361, h4369, hlam]
                      · linarith only [h3633, h3927, h4368, hc15, hlam, hphi, u5elo4]
                    · linarith only [h3095, h3928, h4361, h4364, h4367, hc01, hc12, hlam, hphi]
                  · linarith only [h3928, h4364, h4366, hc02, hc25, hlam, hphi]
                · linarith only [h0, h3927, h3928, h4364, h4365, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4407 | h4407
                · linarith only [h0, h3927, h4291, h4364, h4407, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4409 | h4409
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4410 | h4410
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4411 | h4411
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4412 | h4412
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4413 | h4413
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4414 | h4414
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4415 | h4415
                              · rcases h0bigk with h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c | h4416c
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h0, hlam, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3095, hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3633, hlam, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h0, h4407, h4412, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h0, h4407, h4412, hc01, hc23, hlam, hphi, ht12, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3928, hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h4291, hlam, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h0, h3927, h4407, h4409, h4412, h4413, h4415, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3095, h3927, h4364, h4409, h4413, h4415, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3095, h4364, hc02, hc23, hlam, hphi, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3095, h3633, h3927, h4364, h4409, h4413, h4415, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  rcases p4416_3 (m.d 0 1) (by simp) with h4431 | h4431
                                  · linarith only [h3095, h4431, hlam]
                                  · linarith only [h3927, h4431, hlam]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3927, h4409, h4413, h4415, hc04, hc45, hlam, hphi, ht0b, ht5b, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h0, h3633, h3927, h4364, h4409, h4410, h4413, h4415, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h4361, hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  rcases p4416_3 (m.d 0 1) (by simp) with h4438 | h4438
                                  · linarith only [h3633, h4438, hlam]
                                  · linarith only [h3927, h4438, hlam]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h3927, hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h4360, hlam, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h4362, hlam, p4416_0]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [h4363, hlam, p4416_1]
                                · have p4416_0 := h4416c.1
                                  have p4416_1 := h4416c.2.1
                                  have p4416_2 := h4416c.2.2.1
                                  have p4416_3 := h4416c.2.2.2
                                  linarith only [hlam, p4416_0]
                              · linarith only [h0, h3927, h4407, h4411, h4412, h4415, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h3927, h4407, h4411, h4414, hlam]
                          · linarith only [h0, h4407, h4412, h4413, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h3095, h4361, h4364, h4412, hlam]
                      · linarith only [h3633, h3927, h4409, h4411, hc25, hlam, hphi, u5elo4]
                    · linarith only [h3095, h4361, h4410, hlam]
                  · linarith only [h0, h3927, h4409, hc15, hlam, hphi, u5elo2]
            · linarith only [h3633, h3927, h4363, hc15, hlam, hphi, u5elo4]
          · linarith only [h3095, h3927, h4362, hc15, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4455 | h4455
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4456 | h4456
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4457 | h4457
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4458 | h4458
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4459 | h4459
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4460 | h4460
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4461 | h4461
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4462 | h4462
                        · linarith only [h0, h3927, h3928, h4361, h4457, h4459, h4462, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h3927, h3928, h4459, h4460, h4462, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h3633, h3927, h4459, h4461, hc25, hlam, hphi, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4466 | h4466
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4467 | h4467
                        · linarith only [h0, h3927, h3928, h4361, h4457, h4459, h4467, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4469 | h4469
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4470 | h4470
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4471 | h4471
                              · rcases h0bigk with h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c | h4472c
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h0, hlam, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3095, hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3633, hlam, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h0, h3927, h3928, h4459, h4469, h4471, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3928, hc01, hc23, hlam, hphi, ht12, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3928, hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h4291, hlam, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3095, h3927, h3928, h4459, h4460, h4469, h4471, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3095, h3927, h4459, h4460, h4469, h4471, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3095, h4460, hc02, hc34, hlam, hphi, ht23, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h4361, hlam, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3095, h3927, h4459, h4460, h4469, h4471, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3927, h4459, h4469, h4471, hc04, hc45, hlam, hphi, ht0b, ht5b, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h0, h3927, h4291, h4459, h4469, h4471, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h4361, hc03, hc34, hlam, hphi, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3927, h4291, h4458, h4459, h4469, h4471, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h3927, hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h4360, hlam, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h4455, hlam, p4472_0]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [h4456, hlam, p4472_1]
                                · have p4472_0 := h4472c.1
                                  have p4472_1 := h4472c.2.1
                                  have p4472_2 := h4472c.2.2.1
                                  have p4472_3 := h4472c.2.2.2
                                  linarith only [hlam, p4472_0]
                              · linarith only [h4457, h4460, h4471, hc23, hlam, hphi, ht34, ht45, u5elo4]
                            · linarith only [h0, h3927, h3928, h4466, h4467, h4470, hlam]
                          · linarith only [h0, h3928, h4469, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h3633, h3927, h4459, h4466, hc25, hlam, hphi, u5elo4]
                  · linarith only [h4458, h4459, hc24, hlam, hphi, ht45, u5elo2]
                · linarith only [h0, h3927, h3928, h4457, h4458, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4504 | h4504
                · linarith only [h0, h3927, h4291, h4457, h4504, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4506 | h4506
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4507 | h4507
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4508 | h4508
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4509 | h4509
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4510 | h4510
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4511 | h4511
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4512 | h4512
                              · rcases h0bigk with h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h0, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3095, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3633, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h0, h3927, h3928, h4361, h4506, h4507, h4510, h4512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3928, h4361, h4507, hc01, hc13, hlam, hphi, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3928, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4291, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3927, h3928, h4361, h4506, h4507, h4510, h4512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3927, h4361, h4506, h4507, h4510, h4512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4361, h4507, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4361, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3927, h4361, h4506, h4507, h4510, h4512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3927, h4506, h4510, h4512, hc04, hc45, hlam, hphi, ht0b, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h0, h3927, h4506, h4510, h4512, hc04, hc45, hlam, hphi, ht0b, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4361, h4507, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3927, h4361, h4506, h4507, h4510, h4512, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h3927, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4360, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4455, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4456, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                              · linarith only [h3633, h3927, h4361, h4512, hc15, hlam, hphi, u5elo4]
                            · linarith only [h0, h3927, h4291, h4508, h4511, hlam]
                          · linarith only [h0, h3928, h4361, h4457, h4507, h4510, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h4457, h4507, h4509, hlam]
                      · linarith only [h3633, h3927, h4506, h4508, hc25, hlam, hphi, u5elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4544 | h4544
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4545 | h4545
                        · linarith only [h0, h3927, h4457, h4506, h4507, h4545, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h3927, h4457, h4506, h4545, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h0, h3927, h4457, h4506, h4507, h4544, hc25, hlam, hphi, u5elo4]
                  · linarith only [h0, h3927, h4506, hc15, hlam, hphi, u5elo2]
            · linarith only [h0, h3927, h3928, h4361, h4456, hc15, hlam, hphi, u5elo4]
          · linarith only [h0, h3927, h3928, h4455, hc15, hlam, hphi, u5elo3]
      · linarith only [h0, h3927, h4360, hc15, hlam, hphi, u5elo2]

end R2N4
