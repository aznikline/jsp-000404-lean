import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3885 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h3886 | h3886
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3887 | h3887
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3888 | h3888
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3889 | h3889
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3890 | h3890
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3891 | h3891
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3892 | h3892
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3893 | h3893
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3894 | h3894
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3895 | h3895
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3896 | h3896
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3897 | h3897
                        · rcases h5bigk with h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c | h3898c
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3355, hlam, p3898_1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h0, h3888, h3889, h3895, hc35, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h0, h3888, h3889, hc35, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h0, h3888, h3889, hc45, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo4]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3890, h3895, hc35, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3890, hc35, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3889, h3893, hc45, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3886, hlam, p3898_1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3890, hlam, p3898_1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3886, hc02, hc35, hlam, hphi, ht0b, ht5b, p3898_1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3889, h3896, hc45, hlam, hphi, ht01, ht0b, ht5b, p3898_1, u1elo1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3887, hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3892, hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3895, hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3887, hc03, hc45, hlam, hphi, ht0b, ht5b, p3898_1]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3888, hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3893, hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3896, hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [h3897, hlam, p3898_0]
                          · have p3898_0 := h3898c.1
                            have p3898_1 := h3898c.2.1
                            have p3898_2 := h3898c.2.2.1
                            have p3898_3 := h3898c.2.2.2
                            linarith only [hlam, p3898_0]
                        · linarith only [h3889, h3896, h3897, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3925 | h3925
                        · linarith only [h3891, h3896, h3925, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases h5bigk with h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c | h3927c
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3355, hlam, p3927_1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3355, h3889, h3893, hc25, hlam, hphi, ht01, ht0b, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3355, h3889, h3893, hc35, hlam, hphi, ht01, ht0b, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3355, h3889, h3893, h3896, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3889, h3893, hc05, hlam, hphi, ht01, ht0b, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3889, h3893, h3895, hc35, hlam, hphi, ht01, ht0b, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3889, h3893, hc35, hlam, hphi, ht01, ht0b, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3889, h3893, h3894, h3896, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3886, hlam, p3927_1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3890, hlam, p3927_1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3886, hc02, hc35, hlam, hphi, ht0b, ht5b, p3927_1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3896, hlam, p3927_1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3887, hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3892, hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3895, hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3925, hlam, p3927_1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3888, hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3893, hlam, p3927_0]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h3355, h3888, h3889, h3893, hc25, hlam, hphi, ht01, ht0b, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [h0, h3888, h3889, hc35, hlam, hphi, ht01, ht0b, ht5b, p3927_1, u1elo1]
                          · have p3927_0 := h3927c.1
                            have p3927_1 := h3927c.2.1
                            have p3927_2 := h3927c.2.2.1
                            have p3927_3 := h3927c.2.2.2
                            linarith only [hlam, p3927_0]
                    · linarith only [h3892, h3894, h3895, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3954 | h3954
                    · linarith only [h3891, h3894, h3954, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3956 | h3956
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3957 | h3957
                        · rcases h5bigk with h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c | h3958c
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3355, hlam, p3958_1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3355, h3889, h3893, h3954, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3355, h3889, h3893, hc35, hlam, hphi, ht01, ht0b, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3355, h3889, h3893, hc45, hlam, hphi, ht01, ht0b, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3889, h3893, hc05, hlam, hphi, ht01, ht0b, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3889, h3893, h3954, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3889, h3893, hc35, hlam, hphi, ht01, ht0b, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3889, h3893, hc45, hlam, hphi, ht01, ht0b, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3886, hlam, p3958_1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3890, hlam, p3958_1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3954, hlam, p3958_1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3886, hc02, hc45, hlam, hphi, ht0b, ht5b, p3958_1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3887, hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3892, hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3355, h3887, h3889, h3893, hc25, hlam, hphi, ht01, ht0b, ht5b, p3958_1, u1elo1]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3891, h3957, hc45, hlam, hphi, ht01, ht0b, ht5b, p3958_1, u1elo2]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3888, hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3893, hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3956, hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [h3957, hlam, p3958_0]
                          · have p3958_0 := h3958c.1
                            have p3958_1 := h3958c.2.1
                            have p3958_2 := h3958c.2.2.1
                            have p3958_3 := h3958c.2.2.2
                            linarith only [hlam, p3958_0]
                        · linarith only [h3889, h3956, h3957, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3985 | h3985
                        · linarith only [h3891, h3894, h3956, h3985, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                        · linarith only [h0, h3888, h3889, h3894, h3985, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h3888, h3893, hlam]
              · linarith only [h0, h3355, h3887, h3891, h3892, hc01, hlam, hphi, u1elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3990 | h3990
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3991 | h3991
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3992 | h3992
                  · linarith only [h3355, h3891, h3990, h3992, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3994 | h3994
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3995 | h3995
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3996 | h3996
                        · rcases h5bigk with h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c | h3997c
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3355, hlam, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3355, h3990, hc25, hlam, hphi, ht01, ht0b, ht5b, p3997_1, u1elo2]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3355, h3891, h3990, h3996, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3355, h3891, h3990, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3891, h3990, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3891, h3990, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3891, h3990, h3996, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3891, h3990, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3886, hlam, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3890, hlam, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3886, h3996, hc02, hc45, hlam, hphi, ht0b, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3885, h3992, h3994, hc02, hc45, hlam, hphi, ht0b, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3887, hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3990, hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3994, hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3887, hc03, hc45, hlam, hphi, ht0b, ht5b, p3997_1]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3888, hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3991, hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3995, hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [h3996, hlam, p3997_0]
                          · have p3997_0 := h3997c.1
                            have p3997_1 := h3997c.2.1
                            have p3997_2 := h3997c.2.2.1
                            have p3997_3 := h3997c.2.2.2
                            linarith only [hlam, p3997_0]
                        · linarith only [h3355, h3891, h3990, h3996, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h3888, h3889, h3992, h3994, h3995, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · linarith only [h3891, h3990, h3994, hc23, hc34, hlam, hphi]
                · linarith only [h0, h3888, h3991, hlam]
              · linarith only [h3355, h3887, h3990, hlam]
          · linarith only [h0, h3355, h3886, h3889, h3890, hc01, hlam, hphi, u1elo4]
        · linarith only [h0, h3885, h3889, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4030 | h4030
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4031 | h4031
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4032 | h4032
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4033 | h4033
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4034 | h4034
                · linarith only [h0, h3888, h4030, h4034, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4036 | h4036
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4037 | h4037
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4038 | h4038
                      · linarith only [h0, h4034, h4038, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4040 | h4040
                        · linarith only [h0, h4034, h4040, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h5bigk with h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c | h4042c
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [hlam, p4042_0]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3355, hlam, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3355, h4033, hc25, hlam, hphi, ht01, ht0b, ht5b, p4042_1, u1elo2]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3355, h4033, h4040, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4042_1, u1elo2]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3888, hlam, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4033, hc05, hlam, hphi, ht01, ht0b, ht5b, p4042_1, u1elo2]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [hlam, p4042_0]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4033, hc25, hlam, hphi, ht01, ht0b, ht5b, p4042_1, u1elo2]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4033, h4040, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4042_1, u1elo2]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4034, hlam, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3886, hlam, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4031, hlam, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [hlam, p4042_0]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3886, h4040, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4038, hlam, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3887, hlam, p4042_0]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4033, hlam, p4042_0]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4037, hlam, p4042_0]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [hlam, p4042_0]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4040, hlam, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4037, h4040, hc34, hc45, hlam, hphi, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [h4040, hc34, hc45, hlam, hphi, p4042_1]
                          · have p4042_0 := h4042c.1
                            have p4042_1 := h4042c.2.1
                            have p4042_2 := h4042c.2.2.1
                            have p4042_3 := h4042c.2.2.2
                            linarith only [hlam, p4042_0]
                    · linarith only [h4033, h4036, h4037, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4069 | h4069
                    · linarith only [h4032, h4036, h4069, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4071 | h4071
                      · linarith only [h3885, h3888, h4071, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4073 | h4073
                        · linarith only [h0, h4032, h4034, h4073, hc01, hlam, hphi, u1elo2]
                        · rcases h5bigk with h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c | h4075c
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [hlam, p4075_0]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3355, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3355, h4071, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4075_1, u1elo4]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3355, h4036, h4073, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4075_1, u1elo4]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3888, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p4075_1, u1elo4]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [hlam, p4075_0]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4031, h4071, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4075_1, u1elo1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4031, h4036, h4073, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4075_1, u1elo1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4034, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3886, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4031, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [hlam, p4075_0]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4069, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4071, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3887, hlam, p4075_0]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4033, hlam, p4075_0]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4036, h4071, hc23, hc35, hlam, hphi, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [hlam, p4075_0]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4073, hlam, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4036, h4071, hc23, hc45, hlam, hphi, ht34, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [h4069, hc23, hc45, hlam, hphi, ht34, p4075_1]
                          · have p4075_0 := h4075c.1
                            have p4075_1 := h4075c.2.1
                            have p4075_2 := h4075c.2.2.1
                            have p4075_3 := h4075c.2.2.2
                            linarith only [hlam, p4075_0]
              · linarith only [h0, h3355, h3887, h4031, h4032, h4033, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4102 | h4102
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4103 | h4103
                · linarith only [h0, h3888, h4030, h4103, hc01, hlam, hphi, u1elo1]
                · linarith only [h4032, h4102, h4103, hlam]
              · linarith only [h3355, h3887, h4102, hlam]
          · linarith only [h0, h3355, h3886, h4030, h4031, hc01, hlam, hphi, u1elo4]
        · linarith only [h0, h3885, h4030, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4109 | h4109
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4110 | h4110
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4111 | h4111
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4112 | h4112
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4113 | h4113
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4114 | h4114
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4115 | h4115
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4116 | h4116
                    · linarith only [h3886, h3887, h4116, hlam]
                    · linarith only [h4113, h4115, h4116, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4119 | h4119
                    · linarith only [h3887, h4112, h4115, h4119, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4121 | h4121
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4122 | h4122
                        · rcases h5bigk with h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c | h4123c
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3355, hlam, p4123_1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3355, h4114, h4119, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4123_1, u1elo3]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3887, hlam, p4123_1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3355, h4114, hc45, hlam, hphi, ht01, ht0b, ht5b, p4123_1, u1elo3]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4114, hc05, hlam, hphi, ht01, ht0b, ht5b, p4123_1, u1elo3]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4110, h4114, h4119, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4123_1, u1elo1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3887, h4110, h4114, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4123_1, u1elo1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4110, h4114, hc45, hlam, hphi, ht01, ht0b, ht5b, p4123_1, u1elo1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3886, hlam, p4123_1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4111, hlam, p4123_1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4119, hlam, p4123_1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3886, hc02, hc45, hlam, hphi, ht0b, ht5b, p4123_1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p4123_1]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4113, hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4113, hc25, hlam, hphi, ht01, ht0b, ht5b, p4123_1, u1elo2]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4112, h4122, hc45, hlam, hphi, ht01, ht0b, ht5b, p4123_1, u1elo2]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4109, hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4114, hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4121, hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [h4122, hlam, p4123_0]
                          · have p4123_0 := h4123c.1
                            have p4123_1 := h4123c.2.1
                            have p4123_2 := h4123c.2.2.1
                            have p4123_3 := h4123c.2.2.2
                            linarith only [hlam, p4123_0]
                        · linarith only [h0, h4109, h4110, h4115, h4122, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4150 | h4150
                        · linarith only [h4112, h4121, h4150, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · linarith only [h0, h4109, h4110, h4115, h4150, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h4109, h4114, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4154 | h4154
                · linarith only [h4112, h4113, h4154, hlam]
                · linarith only [h0, h4109, h4154, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4157 | h4157
              · linarith only [h3887, h4112, h4157, hc03, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4159 | h4159
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4160 | h4160
                  · linarith only [h0, h4110, h4112, h4160, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4162 | h4162
                    · linarith only [h4157, h4160, h4162, hc13, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4164 | h4164
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4165 | h4165
                        · rcases h5bigk with h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c | h4166c
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h3355, hlam, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h0, h4109, h4162, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4166_1, u1elo3]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h3887, hlam, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo4]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo4]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4111, h4162, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4166_1, u1elo1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4157, hlam, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4110, h4159, hc45, hlam, hphi, ht01, ht0b, ht5b, p4166_1, u1elo1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h3886, hlam, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4111, hlam, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4162, hlam, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h3886, hc02, hc45, hlam, hphi, ht0b, ht5b, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4162, hc23, hc35, hlam, hphi, p4166_1]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            rcases p4166_3 (m.d 0 5) (by simp) with h4186 | h4186
                            · linarith only [h3887, h4186, hlam]
                            · linarith only [h4109, h4186, hlam]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4109, hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4159, hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4164, hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [h4165, hlam, p4166_0]
                          · have p4166_0 := h4166c.1
                            have p4166_1 := h4166c.2.1
                            have p4166_2 := h4166c.2.2.1
                            have p4166_3 := h4166c.2.2.2
                            linarith only [hlam, p4166_0]
                        · linarith only [h0, h4109, h4110, h4112, h4165, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4195 | h4195
                        · rcases h5bigk with h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c | h4196c
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [hlam, p4196_0]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h3355, hlam, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h0, h4109, h4110, h4160, h4164, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4196_1, u1elo1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h3887, hlam, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h0, h4109, h4110, hc45, hlam, hphi, ht01, ht0b, ht5b, p4196_1, u1elo1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4110, h4159, hc05, hlam, hphi, ht01, ht0b, ht5b, p4196_1, u1elo1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [hlam, p4196_0]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4110, h4159, h4160, h4164, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4196_1, u1elo1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4157, hlam, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4110, h4159, hc45, hlam, hphi, ht01, ht0b, ht5b, p4196_1, u1elo1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h3886, hlam, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4111, hlam, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [hlam, p4196_0]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4162, hlam, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4164, hlam, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h3355, h4195, hc01, hc34, hlam, hphi, ht12, ht23, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h3355, h4195, hc01, hc34, hlam, hphi, ht12, ht23, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4160, h4164, h4195, hc23, hc34, hlam, hphi, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [hlam, p4196_0]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4160, h4164, h4195, hc23, hc34, hlam, hphi, p4196_1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4109, hlam, p4196_0]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4159, hlam, p4196_0]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h0, h4109, h4110, h4160, h4164, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4196_1, u1elo1]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [h4195, hlam, p4196_0]
                          · have p4196_0 := h4196c.1
                            have p4196_1 := h4196c.2.1
                            have p4196_2 := h4196c.2.2.1
                            have p4196_3 := h4196c.2.2.2
                            linarith only [hlam, p4196_0]
                        · linarith only [h0, h4109, h4110, h4112, h4195, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                · linarith only [h0, h4109, h4159, hlam]
          · linarith only [h0, h3355, h3886, h4110, h4111, hc01, hlam, hphi, u1elo4]
        · linarith only [h0, h3885, h4110, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4226 | h4226
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4227 | h4227
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4228 | h4228
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4229 | h4229
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4230 | h4230
                · linarith only [h0, h4109, h4226, h4230, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4232 | h4232
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4233 | h4233
                    · linarith only [h3886, h3887, h4233, hlam]
                    · linarith only [h4229, h4232, h4233, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4236 | h4236
                    · linarith only [h3887, h4232, h4236, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4238 | h4238
                      · linarith only [h0, h4230, h4238, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4240 | h4240
                        · linarith only [h0, h4228, h4230, h4240, hc01, hlam, hphi, u1elo2]
                        · rcases h5bigk with h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c | h4242c
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [hlam, p4242_0]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h3355, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h3355, h4227, hc25, hlam, hphi, ht01, ht0b, ht5b, p4242_1, u1elo1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h3887, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4109, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4227, hc05, hlam, hphi, ht01, ht0b, ht5b, p4242_1, u1elo1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [hlam, p4242_0]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4227, hc25, hlam, hphi, ht01, ht0b, ht5b, p4242_1, u1elo1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h3887, h4109, h4227, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p4242_1, u1elo1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4230, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h3886, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4227, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [hlam, p4242_0]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4236, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4238, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h0, h4109, hc01, hc35, hlam, hphi, ht12, ht23, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4229, hlam, p4242_0]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4229, hc25, hlam, hphi, ht01, ht0b, ht5b, p4242_1, u1elo2]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [hlam, p4242_0]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4240, hlam, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h0, h4109, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h4236, hc23, hc45, hlam, hphi, ht34, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [h3887, hc03, hc45, hlam, hphi, ht34, p4242_1]
                          · have p4242_0 := h4242c.1
                            have p4242_1 := h4242c.2.1
                            have p4242_2 := h4242c.2.2.1
                            have p4242_3 := h4242c.2.2.2
                            linarith only [hlam, p4242_0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4268 | h4268
                · linarith only [h0, h4109, h4228, h4268, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4270 | h4270
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4271 | h4271
                    · linarith only [h0, h4228, h4229, h4271, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4273 | h4273
                      · linarith only [h0, h4268, h4273, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4275 | h4275
                        · linarith only [h0, h4268, h4270, h4275, hc01, hc23, hlam, hphi, ht12]
                        · rcases h5bigk with h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c | h4277c
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [hlam, p4277_0]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3355, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3355, h4227, h4271, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4277_1, u1elo1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3887, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4109, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4227, hc05, hlam, hphi, ht01, ht0b, ht5b, p4277_1, u1elo1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [hlam, p4277_0]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4227, h4270, h4271, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4277_1, u1elo1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4229, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4268, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3886, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4227, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [hlam, p4277_0]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4271, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4273, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3886, h4270, h4271, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3355, h4275, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4270, h4271, h4275, hc34, hc45, hlam, hphi, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [hlam, p4277_0]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4275, hlam, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3886, h4270, h4271, hc34, hc45, hlam, hphi, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h0, h4228, h4229, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h4270, h4271, hc34, hc45, hlam, hphi, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [h3887, hc03, hc45, hlam, hphi, ht34, p4277_1]
                          · have p4277_0 := h4277c.1
                            have p4277_1 := h4277c.2.1
                            have p4277_2 := h4277c.2.2.1
                            have p4277_3 := h4277c.2.2.2
                            linarith only [hlam, p4277_0]
                  · linarith only [h4228, h4229, h4270, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4304 | h4304
              · linarith only [h3887, h4228, h4304, hc03, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4306 | h4306
                · linarith only [h0, h4109, h4306, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4308 | h4308
                  · linarith only [h0, h3885, h4228, h4308, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4310 | h4310
                    · linarith only [h3887, h4308, h4310, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4312 | h4312
                      · linarith only [h4109, h4226, h4312, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4314 | h4314
                        · linarith only [h0, h4306, h4314, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h5bigk with h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c | h4316c
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [hlam, p4316_0]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h3355, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h3355, h4227, hc25, hlam, hphi, ht01, ht0b, ht5b, p4316_1, u1elo1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h3887, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4109, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4227, hc05, hlam, hphi, ht01, ht0b, ht5b, p4316_1, u1elo1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [hlam, p4316_0]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4227, hc25, hlam, hphi, ht01, ht0b, ht5b, p4316_1, u1elo1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4304, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4306, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h3886, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4227, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [hlam, p4316_0]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4310, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4312, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h0, h4109, hc01, hc35, hlam, hphi, ht12, ht23, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4310, hc23, hc35, hlam, hphi, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [hlam, p4316_0]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4314, hlam, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h0, h4109, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h0, h4306, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h4310, hc23, hc45, hlam, hphi, ht34, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [h3887, hc03, hc45, hlam, hphi, ht34, p4316_1]
                          · have p4316_0 := h4316c.1
                            have p4316_1 := h4316c.2.1
                            have p4316_2 := h4316c.2.2.1
                            have p4316_3 := h4316c.2.2.2
                            linarith only [hlam, p4316_0]
          · linarith only [h0, h3355, h3886, h4226, h4227, hc01, hlam, hphi, u1elo4]
        · linarith only [h0, h3885, h4226, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h4344 | h4344
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4345 | h4345
      · linarith only [h3885, h3886, h4345, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4347 | h4347
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4348 | h4348
          · linarith only [h3885, h3886, h4348, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4350 | h4350
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4351 | h4351
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4352 | h4352
                · linarith only [h0, h4345, h4347, h4348, h4351, h4352, hc01, hlam, hphi, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4354 | h4354
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4355 | h4355
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4356 | h4356
                      · linarith only [h0, h3885, h4352, h4356, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4358 | h4358
                        · linarith only [h0, h4347, h4348, h4356, h4358, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h5bigk with h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c | h4360c
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h3355, hlam, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h3886, hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h3355, h4351, h4358, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4360_1, u1elo2]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4345, hlam, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4351, hc05, hlam, hphi, ht01, ht0b, ht5b, p4360_1, u1elo2]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4348, hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4351, h4358, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4360_1, u1elo2]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4352, hlam, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h3885, h3886, h4354, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h3355, h4356, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4356, h4358, hc34, hc45, hlam, hphi, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4356, hlam, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4344, hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4351, hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4355, hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [hlam, p4360_0]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4358, hlam, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h3885, h3886, h4354, hc34, hc45, hlam, hphi, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h0, h4347, h4348, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h3885, h3886, h4354, hc34, hc45, hlam, hphi, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [h4358, hc34, hc45, hlam, hphi, p4360_1]
                          · have p4360_0 := h4360c.1
                            have p4360_1 := h4360c.2.1
                            have p4360_2 := h4360c.2.2.1
                            have p4360_3 := h4360c.2.2.2
                            linarith only [hlam, p4360_0]
                    · linarith only [h4351, h4354, h4355, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4387 | h4387
                    · linarith only [h4350, h4354, h4387, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                    · linarith only [h3886, h4344, h4387, hlam]
              · linarith only [h0, h3355, h4344, h4350, h4351, hc01, hlam, hphi, u1elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4391 | h4391
              · linarith only [h4347, h4348, h4350, h4391, hlam]
              · linarith only [h3355, h4344, h4391, hlam]
        · linarith only [h3885, h3886, h4347, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4395 | h4395
      · linarith only [h3885, h3886, h4395, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4397 | h4397
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4398 | h4398
          · linarith only [h3885, h3886, h4398, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4400 | h4400
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4401 | h4401
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4402 | h4402
                · linarith only [h0, h4395, h4402, hc01, hlam, hphi, u1elo3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4404 | h4404
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4405 | h4405
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4406 | h4406
                      · linarith only [h0, h3885, h4402, h4406, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4408 | h4408
                        · linarith only [h3885, h3886, h4344, h4398, h4401, h4404, h4406, h4408, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                        · rcases h5bigk with h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c | h4410c
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3355, hlam, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3886, hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4344, hlam, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4395, hlam, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3886, h4401, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4410_1, u1elo2]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4398, hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4344, h4401, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4410_1, u1elo2]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4402, hlam, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3885, h3886, h4404, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3355, h4406, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3885, h3886, h4344, h4404, h4406, hc34, hc45, hlam, hphi, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4406, hlam, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3885, h3886, h4401, h4404, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4410_1, u1elo2]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4401, hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4405, hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [hlam, p4410_0]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h4408, hlam, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3885, h3886, h4404, hc34, hc45, hlam, hphi, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h0, h4397, h4398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3885, h3886, h4404, hc34, hc45, hlam, hphi, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [h3885, h3886, h4344, h4404, hc34, hc45, hlam, hphi, p4410_1]
                          · have p4410_0 := h4410c.1
                            have p4410_1 := h4410c.2.1
                            have p4410_2 := h4410c.2.2.1
                            have p4410_3 := h4410c.2.2.2
                            linarith only [hlam, p4410_0]
                    · linarith only [h4401, h4404, h4405, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4437 | h4437
                    · linarith only [h4344, h4404, h4437, hc03, hc34, hlam, hphi]
                    · linarith only [h0, h4397, h4398, h4401, h4437, hc01, hlam, hphi, u1elo2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4440 | h4440
                · linarith only [h0, h4395, h4397, h4440, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4442 | h4442
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4443 | h4443
                    · linarith only [h0, h4400, h4401, h4443, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4445 | h4445
                      · linarith only [h3885, h4395, h4445, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4447 | h4447
                        · linarith only [h3355, h3885, h3886, h4398, h4442, h4445, h4447, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                        · rcases h5bigk with h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [hlam, p4449_0]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3355, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3886, hlam, p4449_0]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4344, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4395, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3886, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4449_1, u1elo4]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [hlam, p4449_0]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4398, hlam, p4449_0]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4401, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4440, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3885, h3886, h4442, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3355, h4443, h4447, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [hlam, p4449_0]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4443, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4445, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3885, h3886, h4442, h4447, hc34, hc45, hlam, hphi, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4398, h4447, hc12, hc45, hlam, hphi, ht23, ht34, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3885, h3886, h4442, h4447, hc34, hc45, hlam, hphi, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [hlam, p4449_0]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4447, hlam, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h3885, h3886, h4442, hc34, hc45, hlam, hphi, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h0, h4397, h4398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h0, h4397, h4398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [h4443, hc23, hc45, hlam, hphi, ht34, p4449_1]
                          · have p4449_0 := h4449c.1
                            have p4449_1 := h4449c.2.1
                            have p4449_2 := h4449c.2.2.1
                            have p4449_3 := h4449c.2.2.2
                            linarith only [hlam, p4449_0]
                  · linarith only [h4400, h4401, h4442, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4476 | h4476
              · linarith only [h4344, h4400, h4476, hc03, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4478 | h4478
                · linarith only [h0, h4395, h4397, h4478, hc01, hlam, hphi, u1elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4480 | h4480
                  · linarith only [h0, h3885, h4400, h4480, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4482 | h4482
                    · linarith only [h4344, h4480, h4482, hc03, hc34, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4484 | h4484
                      · linarith only [h3355, h3885, h3886, h4395, h4484, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4486 | h4486
                        · linarith only [h0, h4397, h4398, h4484, h4486, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases h5bigk with h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c | h4488c
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [hlam, p4488_0]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3355, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3886, hlam, p4488_0]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4344, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4395, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3885, h3886, h4480, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4488_1, u1elo4]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [hlam, p4488_0]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4398, hlam, p4488_0]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4476, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4478, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3885, h3886, h4480, h4482, h4486, hc23, hc45, hlam, hphi, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3355, h4482, h4486, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [hlam, p4488_0]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4482, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4484, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3885, h3886, h4480, h4486, hc23, hc45, hlam, hphi, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4398, h4486, hc12, hc45, hlam, hphi, ht23, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3885, h3886, h4480, h4486, hc23, hc45, hlam, hphi, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [hlam, p4488_0]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4486, hlam, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h3885, h3886, h4480, hc23, hc45, hlam, hphi, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h0, h4397, h4398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h0, h4397, h4398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [h4344, hc03, hc45, hlam, hphi, ht34, p4488_1]
                          · have p4488_0 := h4488c.1
                            have p4488_1 := h4488c.2.1
                            have p4488_2 := h4488c.2.2.1
                            have p4488_3 := h4488c.2.2.2
                            linarith only [hlam, p4488_0]
        · linarith only [h3885, h3886, h4397, hc12, hc25, hlam, hphi]

end R2N4
