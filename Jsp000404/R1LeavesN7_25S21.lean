import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S20

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5416000 in
set_option maxHeartbeats 5416000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3095 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3633 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3927 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4554 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h5058 | h5058
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5059 | h5059
    · linarith only [h4553, h4554, h5059, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5061 | h5061
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5062 | h5062
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5063 | h5063
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5064 | h5064
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5065 | h5065
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5066 | h5066
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5067 | h5067
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5068 | h5068
                    · linarith only [h4553, h4554, h5059, h5064, h5068, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5070 | h5070
                      · linarith only [h4553, h4554, h5063, h5066, h5068, h5070, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h4553, h4554, h5061, h5063, h5066, h5068, h5070, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h3633, h5067, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5074 | h5074
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5075 | h5075
                    · linarith only [h3095, h5066, h5075, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5077 | h5077
                      · linarith only [h4553, h4554, h5064, h5077, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h4553, h4554, h5061, h5064, h5077, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h4553, h4554, h5061, h5062, h5064, h5074, hlam]
              · linarith only [h4554, h5058, h5064, h5065, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5082 | h5082
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5083 | h5083
                · linarith only [h5059, h5061, h5063, h5064, h5083, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5085 | h5085
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5086 | h5086
                    · linarith only [h0, h3633, h4553, h5064, h5083, h5086, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5088 | h5088
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5089 | h5089
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5090 | h5090
                          · rcases h0bigk with h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c | h5091c
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [hlam, p5091_0]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h0, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h3095, hlam, p5091_0]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h3633, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h3927, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [hlam, p5091_0]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h0, h4553, h5064, h5086, h5088, h5090, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h4554, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h0, h5064, h5086, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h4553, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [hlam, p5091_0]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h5059, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h0, h3927, h4553, h5064, h5086, hc01, hc34, hlam, hphi, ht12, ht23, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h3633, hc01, hc14, hlam, hphi, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h4554, h5086, hc02, hc34, hlam, hphi, ht23, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h4553, h4554, h5086, h5088, h5090, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [hlam, p5091_0]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h3927, h4554, h5086, hc01, hc34, hlam, hphi, ht12, ht23, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5091_1, u5elo0]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h5058, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h5061, hlam, p5091_0]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [h5062, hlam, p5091_1]
                            · have p5091_0 := h5091c.1
                              have p5091_1 := h5091c.2.1
                              have p5091_2 := h5091c.2.2.1
                              have p5091_3 := h5091c.2.2.2
                              linarith only [hlam, p5091_0]
                          · linarith only [h0, h4553, h5064, h5086, h5088, h5090, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h3927, h4553, h5062, h5064, h5088, h5089, hc35, hlam, hphi, u5elo1]
                      · linarith only [h3095, h5061, h5063, h5064, h5086, h5088, hc23, hc34, hlam, hphi]
                  · linarith only [h3633, h3927, h5062, h5085, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
              · linarith only [h0, h5082, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h0, h4553, h4554, h5063, hc01, hc24, hlam, hphi, ht12]
        · linarith only [h4553, h4554, h5062, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5124 | h5124
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5125 | h5125
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5126 | h5126
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5127 | h5127
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5128 | h5128
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5129 | h5129
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5130 | h5130
                    · linarith only [h4553, h4554, h5059, h5126, h5130, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5132 | h5132
                      · linarith only [h4553, h4554, h5125, h5128, h5130, h5132, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5134 | h5134
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5135 | h5135
                          · rcases h0bigk with h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c | h5136c
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [hlam, p5136_0]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h0, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h3095, hlam, p5136_0]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h3633, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h3927, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h4554, h5125, h5128, h5130, hc01, hc12, hlam, hphi, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [hlam, p5136_0]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h3095, h4554, h5125, h5128, h5130, hc01, hc12, hlam, hphi, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h4554, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h4554, h5125, h5128, h5130, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h5061, hc01, hc35, hlam, hphi, ht12, ht23, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h4553, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [hlam, p5136_0]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h5059, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h5061, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h3633, hc01, hc14, hlam, hphi, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h4554, h5058, h5125, h5128, h5130, h5132, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h4554, h5125, h5128, h5130, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [hlam, p5136_0]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h3095, h4554, h5061, h5125, h5128, h5130, hc01, hc12, hlam, hphi, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5136_1, u5elo0]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h5058, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h3095, h4554, h5058, h5125, h5128, h5130, hc01, hc12, hlam, hphi, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [h5124, hlam, p5136_1]
                            · have p5136_0 := h5136c.1
                              have p5136_1 := h5136c.2.1
                              have p5136_2 := h5136c.2.2.1
                              have p5136_3 := h5136c.2.2.2
                              linarith only [hlam, p5136_0]
                          · linarith only [h4554, h5058, h5130, h5134, h5135, hlam]
                        · linarith only [h4554, h5058, h5132, h5134, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h3633, h4554, h5058, h5124, h5129, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5165 | h5165
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5166 | h5166
                    · linarith only [h4553, h4554, h5126, h5128, h5166, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5168 | h5168
                      · linarith only [h4553, h4554, h5126, h5168, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5170 | h5170
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5171 | h5171
                          · rcases h0bigk with h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c | h5172c
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [hlam, p5172_0]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h0, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h3095, hlam, p5172_0]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h3633, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h3927, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h4554, h5126, hc01, hc12, hlam, hphi, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [hlam, p5172_0]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h3095, h4554, h5126, hc01, hc12, hlam, hphi, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h4554, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h4554, h5126, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h5061, hc01, hc35, hlam, hphi, ht12, ht23, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h4553, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [hlam, p5172_0]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h5059, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h5061, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h4554, h5126, hc01, hc12, hlam, hphi, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h4554, h5126, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h4554, h5126, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [hlam, p5172_0]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h3095, h4554, h5061, h5126, hc01, hc12, hlam, hphi, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5172_1, u5elo0]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h5058, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h3095, h4554, h5058, h5126, hc01, hc12, hlam, hphi, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [h5124, hlam, p5172_1]
                            · have p5172_0 := h5172c.1
                              have p5172_1 := h5172c.2.1
                              have p5172_2 := h5172c.2.2.1
                              have p5172_3 := h5172c.2.2.2
                              linarith only [hlam, p5172_0]
                          · linarith only [h4554, h5126, h5128, h5171, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h4554, h5058, h5124, h5170, hlam]
                  · linarith only [h4554, h5058, h5124, h5126, h5165, hlam]
              · linarith only [h4554, h5058, h5127, hc12, hc24, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5202 | h5202
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5203 | h5203
                · linarith only [h3095, h5059, h5125, h5126, h5203, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5205 | h5205
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5206 | h5206
                    · linarith only [h0, h4553, h5126, h5203, h5206, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5208 | h5208
                      · linarith only [h4553, h5061, h5208, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5210 | h5210
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5211 | h5211
                          · rcases h0bigk with h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c | h5212c
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [hlam, p5212_0]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h0, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3095, hlam, p5212_0]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3633, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3927, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h0, h5126, h5206, hc01, hc34, hlam, hphi, ht12, ht23, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [hlam, p5212_0]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h0, h5126, h5206, hc03, hc34, hlam, hphi, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h4554, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h0, h5126, h5206, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3095, hc01, hc13, hlam, hphi, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h4553, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [hlam, p5212_0]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h5059, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h5061, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3633, h5126, h5206, hc01, hc34, hlam, hphi, ht12, ht23, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3633, h5126, h5206, hc02, hc34, hlam, hphi, ht23, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3095, h3633, h5126, h5206, hc01, hc34, hlam, hphi, ht12, ht23, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [hlam, p5212_0]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3095, h3633, h5061, h5126, h5206, hc01, hc34, hlam, hphi, ht12, ht23, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5212_1, u5elo0]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h5058, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h3095, h3927, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5212_1, u5elo1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [h5124, hlam, p5212_1]
                            · have p5212_0 := h5212c.1
                              have p5212_1 := h5212c.2.1
                              have p5212_2 := h5212c.2.2.1
                              have p5212_3 := h5212c.2.2.2
                              linarith only [hlam, p5212_0]
                          · linarith only [h5126, h5206, h5211, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h3095, h5124, h5125, h5126, h5210, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h3633, h5124, h5205, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
              · linarith only [h0, h5058, h5202, hlam]
          · linarith only [h0, h4553, h5125, hlam]
        · linarith only [h4554, h5058, h5124, hc25, hlam, hphi, u5elo4]
  · linarith only [h4553, h5058, hc23, hlam, hphi, ht34, ht45, u5elo2]

set_option maxHeartbeats 5416000 in
set_option maxHeartbeats 5416000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3095 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3633 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3927 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h4554 | h4554
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 h3095 h3633 h3927 h4553 h4554
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 h3095 h3633 h3927 h4553 h4554

set_option maxHeartbeats 5416000 in
set_option maxHeartbeats 5416000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s4_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3095 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h3633 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3927 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4553 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h5245 | h5245
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5246 | h5246
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5247 | h5247
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5248 | h5248
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5249 | h5249
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5250 | h5250
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5251 | h5251
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5252 | h5252
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5253 | h5253
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5254 | h5254
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5255 | h5255
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5256 | h5256
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5257 | h5257
                          · linarith only [h4553, h5245, h5250, h5257, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h4553, h5245, h5249, h5250, h5257, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h4553, h5256, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h4553, h5245, h5247, h5255, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h3633, h5254, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h3095, h4553, h5245, h5247, h5250, h5253, hc01, hc12, hlam, hphi]
                · linarith only [h4553, h5246, h5250, h5252, hlam]
              · linarith only [h4553, h5250, h5251, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5266 | h5266
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5267 | h5267
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5268 | h5268
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5269 | h5269
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5270 | h5270
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5271 | h5271
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5272 | h5272
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5273 | h5273
                            · rcases h0bigk with h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c | h5274c
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h0, hlam, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h3095, hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h3633, hlam, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h3927, hlam, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h4553, hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h0, h5245, h5250, h5270, h5273, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h0, h3927, h5250, hc01, hc23, hlam, hphi, ht12, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h4553, hc01, hc23, hlam, hphi, ht12, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h4553, hc02, hc23, hlam, hphi, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h4553, h5245, h5270, h5273, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h3927, h4553, hc01, hc23, hlam, hphi, ht12, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h3633, hc01, hc14, hlam, hphi, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h5245, hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h5247, hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h0, h3927, h5245, h5250, hc01, hc23, hlam, hphi, ht12, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5274_1, u5elo0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h5246, hlam, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h5248, hlam, p5274_0]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [h5249, hlam, p5274_1]
                              · have p5274_0 := h5274c.1
                                have p5274_1 := h5274c.2.1
                                have p5274_2 := h5274c.2.2.1
                                have p5274_3 := h5274c.2.2.2
                                linarith only [hlam, p5274_0]
                            · linarith only [h0, h5245, h5250, h5272, h5273, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5301 | h5301
                            · linarith only [h5270, h5272, h5301, hlam]
                            · rcases h0bigk with h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c | h5303c
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h0, hlam, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h3095, hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h3633, hlam, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h3927, hlam, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h0, h5250, hc01, hc23, hlam, hphi, ht12, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h4553, hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h0, h5249, h5250, h5270, h5272, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h0, h5250, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h3095, h5250, hc01, hc23, hlam, hphi, ht12, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h3095, h5250, hc02, hc23, hlam, hphi, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h3095, h5249, h5250, h5270, h5272, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h3095, h3927, h5250, hc01, hc23, hlam, hphi, ht12, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h0, h5245, h5250, hc01, hc23, hlam, hphi, ht12, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h5245, hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h5247, hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h0, h3927, h5245, h5250, hc01, hc23, hlam, hphi, ht12, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5303_1, u5elo0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h5246, hlam, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h5248, hlam, p5303_0]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [h5249, hlam, p5303_1]
                              · have p5303_0 := h5303c.1
                                have p5303_1 := h5303c.2.1
                                have p5303_2 := h5303c.2.2.1
                                have p5303_3 := h5303c.2.2.2
                                linarith only [hlam, p5303_0]
                        · linarith only [h0, h5245, h5249, h5250, h5271, hc45, hlam, hphi, u5elo3]
                      · linarith only [h3927, h5250, h5266, h5269, h5270, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3633, h5245, h5249, h5250, h5269, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h3095, h5245, h5247, h5250, h5268, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5246, h5267, hlam]
              · linarith only [h0, h5245, h5266, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5335 | h5335
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5336 | h5336
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5337 | h5337
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5338 | h5338
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5339 | h5339
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5340 | h5340
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5341 | h5341
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5342 | h5342
                          · linarith only [h0, h3633, h5245, h5249, h5342, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5344 | h5344
                            · linarith only [h3633, h4553, h5246, h5249, h5335, h5340, h5342, h5344, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c | h5346c
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h0, hlam, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3095, hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3633, hlam, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3927, hlam, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h4553, h5335, hc01, hc12, hlam, hphi, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h4553, hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3633, h4553, h5335, hc01, hc12, hlam, hphi, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3633, h4553, h5249, h5335, h5339, hc01, hc05, hc12, hlam, hphi, p5346_1, u5elo1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3095, hc01, hc13, hlam, hphi, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3633, h4553, h5249, h5335, h5339, hc01, hc02, hc12, hlam, hphi, ht23, ht34, ht45, p5346_1, u5elo1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3633, h4553, h5335, hc01, hc12, hlam, hphi, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h3927, h4553, h5335, hc01, hc12, hlam, hphi, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h5249, h5339, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5346_1, u5elo1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h5245, hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h5247, hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h5249, hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5346_1, u5elo0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h5246, hlam, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h5248, hlam, p5346_0]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [h4553, h5246, h5335, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5346_1]
                              · have p5346_0 := h5346c.1
                                have p5346_1 := h5346c.2.1
                                have p5346_2 := h5346c.2.2.1
                                have p5346_3 := h5346c.2.2.2
                                linarith only [hlam, p5346_0]
                        · linarith only [h4553, h5341, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h4553, h5247, h5340, hlam]
                    · linarith only [h3633, h5339, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h3095, h5247, h5249, h5338, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h4553, h5246, h5337, hc12, hc23, hlam, hphi]
              · linarith only [h4553, h5335, h5336, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5378 | h5378
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5379 | h5379
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5380 | h5380
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5381 | h5381
                    · linarith only [h3633, h5249, h5335, h5378, h5381, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h3633, h5381, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h3095, h5247, h5380, hlam]
                · linarith only [h0, h5379, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h5245, h5378, hlam]
        · linarith only [h4553, h5246, h5248, hc25, hlam, hphi, u5elo3]
      · linarith only [h4553, h5245, h5247, hlam]
    · linarith only [h5245, h5246, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5390 | h5390
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5391 | h5391
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5392 | h5392
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5393 | h5393
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5394 | h5394
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5395 | h5395
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5396 | h5396
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5397 | h5397
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5398 | h5398
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5399 | h5399
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5400 | h5400
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5401 | h5401
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5402 | h5402
                            · rcases h0bigk with h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h0, hlam, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h3095, hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h3633, hlam, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h3927, hlam, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5245, h5394, h5399, hc01, hc12, hlam, hphi, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h4553, hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5245, hlam, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5245, h5394, h5399, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h3095, hc01, hc13, hlam, hphi, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h4553, h5394, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h4553, h5394, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h3927, h4553, h5394, hc01, hc12, hlam, hphi, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h3633, hc01, hc14, hlam, hphi, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5245, h5390, h5394, h5399, h5400, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5391, hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h3927, h5245, h5394, h5399, hc01, hc12, hlam, hphi, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5403_1, u5elo0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5390, hlam, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5392, hlam, p5403_0]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [h5393, hlam, p5403_1]
                              · have p5403_0 := h5403c.1
                                have p5403_1 := h5403c.2.1
                                have p5403_2 := h5403c.2.2.1
                                have p5403_3 := h5403c.2.2.2
                                linarith only [hlam, p5403_0]
                            · linarith only [h5245, h5390, h5394, h5399, h5401, h5402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h5245, h5401, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h5245, h5399, h5400, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h4553, h5390, h5391, h5399, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h3633, h5398, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h3095, h4553, h5391, h5394, h5397, hc01, hc12, hlam, hphi]
                · linarith only [h5245, h5390, h5395, h5396, hlam]
              · linarith only [h4553, h5394, h5395, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5437 | h5437
              · linarith only [h5245, h5390, h5394, h5437, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5439 | h5439
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5440 | h5440
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5441 | h5441
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5442 | h5442
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5443 | h5443
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5444 | h5444
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5445 | h5445
                            · rcases h0bigk with h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h0, hlam, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h3095, hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h3633, hlam, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h3927, hlam, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h0, h5437, h5442, hc01, hc23, hlam, hphi, ht12, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h4553, hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h5245, hlam, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h0, h3927, h5437, h5442, hc01, hc23, hlam, hphi, ht12, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h3095, hc01, hc13, hlam, hphi, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h4553, hc02, hc23, hlam, hphi, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h4553, h5245, h5390, h5443, h5445, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h3927, h4553, hc01, hc23, hlam, hphi, ht12, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h3633, hc01, hc14, hlam, hphi, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h5245, h5390, h5442, h5443, h5445, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h5391, hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h3927, h5245, h5442, hc01, hc23, hlam, hphi, ht12, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5446_1, u5elo0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h5390, hlam, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h5392, hlam, p5446_0]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [h5393, hlam, p5446_1]
                              · have p5446_0 := h5446c.1
                                have p5446_1 := h5446c.2.1
                                have p5446_2 := h5446c.2.2.1
                                have p5446_3 := h5446c.2.2.2
                                linarith only [hlam, p5446_0]
                            · rcases h0bigk with h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c | h5472c
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h0, hlam, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3095, hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3633, hlam, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3927, hlam, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h0, h5437, h5442, hc01, hc23, hlam, hphi, ht12, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h4553, hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h5245, hlam, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h0, h5437, h5442, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3095, h5394, hc01, hc23, hlam, hphi, ht12, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3095, h5390, h5394, h5444, h5445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3095, h3633, h5394, hc01, hc23, hlam, hphi, ht12, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3095, h5390, h5394, h5444, h5445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3633, h5437, h5442, hc01, hc23, hlam, hphi, ht12, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3633, h5390, h5437, h5442, h5444, h5445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h5391, hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h3633, h5390, h5437, h5442, h5444, h5445, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5472_1, u5elo0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h5390, hlam, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h5392, hlam, p5472_0]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [h5393, hlam, p5472_1]
                              · have p5472_0 := h5472c.1
                                have p5472_1 := h5472c.2.1
                                have p5472_2 := h5472c.2.2.1
                                have p5472_3 := h5472c.2.2.2
                                linarith only [hlam, p5472_0]
                          · linarith only [h0, h5390, h5437, h5443, h5444, hc35, hlam, hphi, u5elo4]
                        · linarith only [h3095, h5394, h5443, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h3095, h5391, h5394, h5442, hlam]
                    · linarith only [h3633, h5393, h5441, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                  · linarith only [h3095, h5391, h5440, hlam]
                · linarith only [h0, h5439, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h5245, h5390, h5393, hc25, hlam, hphi, u5elo4]
        · linarith only [h4553, h5390, h5392, hc25, hlam, hphi, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5506 | h5506
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5507 | h5507
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5508 | h5508
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5509 | h5509
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5510 | h5510
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5511 | h5511
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5512 | h5512
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5513 | h5513
                      · linarith only [h4553, h5390, h5391, h5508, h5513, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h4553, h5390, h5511, h5513, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h3633, h5512, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5517 | h5517
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5518 | h5518
                      · linarith only [h3095, h5511, h5518, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5520 | h5520
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5521 | h5521
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5522 | h5522
                            · rcases h0bigk with h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c | h5523c
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [hlam, p5523_0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h0, hlam, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h3095, hlam, p5523_0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h3633, hlam, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h3927, hlam, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h4553, h5508, h5511, hc01, hc34, hlam, hphi, ht12, ht23, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [hlam, p5523_0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h4553, hlam, p5523_0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h5245, hlam, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h4553, h5508, h5511, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h3095, h5511, hc01, hc34, hlam, hphi, ht12, ht23, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h4553, h5508, h5511, hc02, hc34, hlam, hphi, ht23, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [hlam, p5523_0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h5391, hlam, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h3927, h4553, h5508, h5511, hc01, hc34, hlam, hphi, ht12, ht23, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h3633, hc01, hc14, hlam, hphi, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h5390, h5520, h5522, hc04, hc45, hlam, hphi, ht0b, ht5b, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h5391, hc03, hc34, hlam, hphi, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [hlam, p5523_0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h3927, h5391, hc01, hc34, hlam, hphi, ht12, ht23, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5523_1, u5elo0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h5390, hlam, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h5506, hlam, p5523_0]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [h5507, hlam, p5523_1]
                              · have p5523_0 := h5523c.1
                                have p5523_1 := h5523c.2.1
                                have p5523_2 := h5523c.2.2.1
                                have p5523_3 := h5523c.2.2.2
                                linarith only [hlam, p5523_0]
                            · linarith only [h4553, h5390, h5508, h5511, h5520, h5522, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h3633, h4553, h5245, h5390, h5507, h5508, h5511, h5521, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h4553, h5520, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h3633, h5517, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h4553, h5390, h5510, hc12, hc23, hlam, hphi]
              · linarith only [h4553, h5508, h5509, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5555 | h5555
              · linarith only [h5245, h5390, h5508, h5555, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5557 | h5557
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5558 | h5558
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5559 | h5559
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5560 | h5560
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5561 | h5561
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5562 | h5562
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5563 | h5563
                            · rcases h0bigk with h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [hlam, p5564_0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h0, hlam, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h3095, hlam, p5564_0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h3633, hlam, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h3927, hlam, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h0, h5555, h5560, hc01, hc23, hlam, hphi, ht12, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [hlam, p5564_0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h4553, hlam, p5564_0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5245, hlam, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h4553, h5391, h5508, h5558, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5391, h5508, h5558, hc01, hc23, hlam, hphi, ht12, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5391, h5508, h5558, hc02, hc23, hlam, hphi, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [hlam, p5564_0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5391, hlam, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h3927, h5391, h5508, h5558, hc01, hc23, hlam, hphi, ht12, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h3633, h5508, h5558, hc01, hc23, hlam, hphi, ht12, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h3633, h5390, h5508, h5558, h5561, h5563, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5391, h5508, h5558, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [hlam, p5564_0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h3927, h5391, h5508, h5558, hc01, hc23, hlam, hphi, ht12, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5564_1, u5elo0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5390, hlam, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5506, hlam, p5564_0]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [h5507, hlam, p5564_1]
                              · have p5564_0 := h5564c.1
                                have p5564_1 := h5564c.2.1
                                have p5564_2 := h5564c.2.2.1
                                have p5564_3 := h5564c.2.2.2
                                linarith only [hlam, p5564_0]
                            · linarith only [h4553, h5390, h5391, h5561, h5563, hc35, hlam, hphi, u5elo4]
                          · linarith only [h4553, h5390, h5391, h5507, h5508, h5555, h5558, h5562, hc12, hc23, hlam, hphi]
                        · linarith only [h4553, h5391, h5508, h5558, h5561, hc02, hc35, hlam, hphi, ht23]
                      · linarith only [h5508, h5558, h5560, hlam]
                    · linarith only [h3633, h4553, h5390, h5391, h5507, h5508, h5558, h5559, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5595 | h5595
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5596 | h5596
                      · linarith only [h3927, h5508, h5557, h5558, h5596, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h3927, h5508, h5557, h5596, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h3633, h5390, h5507, h5508, h5595, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h3095, h4553, h5390, h5557, hc01, hc13, hlam, hphi]
          · linarith only [h4553, h5390, h5391, h5507, hc25, hlam, hphi, u5elo4]
        · linarith only [h4553, h5390, h5506, hc25, hlam, hphi, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5603 | h5603
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5604 | h5604
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5605 | h5605
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5606 | h5606
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5607 | h5607
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5608 | h5608
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5609 | h5609
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5610 | h5610
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5611 | h5611
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5612 | h5612
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5613 | h5613
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5614 | h5614
                            · rcases h0bigk with h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h0, hlam, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h3095, hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h3633, hlam, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h3927, hlam, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h5390, h5608, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5615_1, u5elo1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h4553, hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h5245, hlam, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h5390, hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h4553, h5606, hc01, hc12, hlam, hphi, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h4553, h5606, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h0, h4553, h5390, h5603, h5606, h5608, h5614, hc01, hc12, hc45, hlam, hphi, p5615_1, u5elo1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h0, h4553, h5390, h5606, hc01, hc12, hlam, hphi, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h3633, hc01, hc14, hlam, hphi, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h0, h5245, hc01, hc24, hlam, hphi, ht12, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h5603, hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h0, h4553, h5390, h5603, h5606, hc01, hc12, hlam, hphi, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5615_1, u5elo0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h0, h5390, hc01, hc25, hlam, hphi, ht12, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h5604, hlam, p5615_0]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [h5605, hlam, p5615_1]
                              · have p5615_0 := h5615c.1
                                have p5615_1 := h5615c.2.1
                                have p5615_2 := h5615c.2.2.1
                                have p5615_3 := h5615c.2.2.2
                                linarith only [hlam, p5615_0]
                            · rcases h0bigk with h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, hlam, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h3095, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h3633, hlam, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h3927, hlam, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h4553, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5245, hlam, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5390, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h4553, h5606, hc01, hc12, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h4553, h5606, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h4553, h5606, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, h4553, h5390, h5606, h5608, hc01, hc05, hc12, hlam, hphi, p5641_1, u5elo1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h3633, h5606, h5609, hc01, hc12, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, h5245, h5606, h5611, hc01, hc12, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5603, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, h5245, h5390, h5606, h5611, hc01, hc12, hlam, hphi, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5641_1, u5elo0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h0, h5390, hc01, hc25, hlam, hphi, ht12, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5604, hlam, p5641_0]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [h5605, hlam, p5641_1]
                              · have p5641_0 := h5641c.1
                                have p5641_1 := h5641c.2.1
                                have p5641_2 := h5641c.2.2.1
                                have p5641_3 := h5641c.2.2.2
                                linarith only [hlam, p5641_0]
                          · linarith only [h0, h5245, h5613, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                        · linarith only [h4553, h5604, h5612, hlam]
                      · linarith only [h4553, h5603, h5611, hlam]
                    · linarith only [h3633, h5610, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h3095, h4553, h5603, h5609, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h4553, h5606, h5608, hc03, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h0, h4553, h5606, h5607, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5674 | h5674
              · linarith only [h0, h5245, h5606, h5674, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5676 | h5676
                · linarith only [h0, h5390, h5606, h5676, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5676, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5679 | h5679
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5680 | h5680
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5681 | h5681
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5682 | h5682
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5683 | h5683
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5684 | h5684
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5685 | h5685
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5686 | h5686
                          · linarith only [h0, h5245, h5605, h5679, h5684, h5686, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h5245, h5683, h5686, hc01, hc14, hlam, hphi]
                        · linarith only [h0, h4553, h5685, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h3095, h4553, h5603, h5679, h5684, hc01, hc12, hlam, hphi]
                    · linarith only [h3633, h5683, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h3095, h5603, h5605, h5682, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h4553, h5679, h5681, hc03, hlam, hphi, ht34, ht45, u5elo2]
              · linarith only [h0, h4553, h5679, h5680, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5695 | h5695
              · linarith only [h0, h5245, h5679, h5695, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5697 | h5697
                · linarith only [h0, h5390, h5679, h5697, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5697, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h5603, h5604, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5701 | h5701
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5702 | h5702
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5703 | h5703
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5704 | h5704
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5705 | h5705
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5706 | h5706
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5707 | h5707
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5708 | h5708
                      · linarith only [h5603, h5701, h5703, h5708, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h4553, h5706, h5708, hc01, hc13, hlam, hphi]
                    · linarith only [h3633, h5707, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5712 | h5712
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5713 | h5713
                      · linarith only [h3095, h5706, h5713, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5715 | h5715
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5716 | h5716
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5717 | h5717
                            · rcases h0bigk with h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c | h5718c
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h0, hlam, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h3095, hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h3633, hlam, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h3927, hlam, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h5390, h5705, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5718_1, u5elo1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h4553, hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h5245, hlam, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h5390, hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h4553, h5703, hc01, hc13, hlam, hphi, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h4553, h5703, h5706, hc02, hc34, hlam, hphi, ht23, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h5603, hlam, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h4553, h5703, h5706, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h5245, h5704, hc01, hc12, hlam, hphi, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h0, h5245, h5704, hc01, hc12, hlam, hphi, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h0, h5245, h5390, h5704, h5705, hc01, hc03, hc12, hlam, hphi, ht34, ht45, p5718_1, u5elo1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h0, h5245, h5390, h5704, hc01, hc12, hlam, hphi, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p5718_1, u5elo0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h0, h5390, hc01, hc25, hlam, hphi, ht12, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h5701, hlam, p5718_0]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [h5702, hlam, p5718_1]
                              · have p5718_0 := h5718c.1
                                have p5718_1 := h5718c.2.1
                                have p5718_2 := h5718c.2.2.1
                                have p5718_3 := h5718c.2.2.2
                                linarith only [hlam, p5718_0]
                            · linarith only [h5706, h5717, hc13, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h0, h3095, h5245, h5701, h5702, h5706, h5716, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h4553, h5701, h5715, hlam]
                    · linarith only [h5245, h5702, h5704, h5712, hlam]
                · linarith only [h0, h5705, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h4553, h5703, h5704, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5750 | h5750
              · linarith only [h0, h5245, h5703, h5750, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5752 | h5752
                · linarith only [h0, h5390, h5703, h5752, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5752, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · linarith only [h5603, h5701, h5702, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5756 | h5756
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5757 | h5757
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5758 | h5758
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5759 | h5759
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5760 | h5760
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5761 | h5761
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5762 | h5762
                      · linarith only [h0, h4553, h5603, h5757, h5762, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h4553, h5760, h5762, hc01, hc13, hlam, hphi]
                    · linarith only [h3633, h5761, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5766 | h5766
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5767 | h5767
                      · linarith only [h3095, h5760, h5767, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5769 | h5769
                        · linarith only [h0, h4553, h5701, h5757, h5760, h5769, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h4553, h5769, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h3633, h5756, h5766, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo0]
                · linarith only [h0, h5759, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h4553, h5757, h5758, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5775 | h5775
              · linarith only [h0, h5245, h5757, h5775, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5777 | h5777
                · linarith only [h0, h5390, h5757, h5777, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5777, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5780 | h5780
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5781 | h5781
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5782 | h5782
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5783 | h5783
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5784 | h5784
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5785 | h5785
                      · linarith only [h0, h4553, h5603, h5780, h5785, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h4553, h5783, h5785, hc01, hc13, hlam, hphi]
                    · linarith only [h3633, h5784, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5789 | h5789
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5790 | h5790
                      · linarith only [h0, h4553, h5603, h5780, h5790, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5792 | h5792
                        · linarith only [h0, h4553, h5701, h5780, h5783, h5792, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h4553, h5792, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h3633, h5789, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h5782, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h4553, h5780, h5781, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h5798 | h5798
              · linarith only [h0, h5245, h5780, h5798, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h5800 | h5800
                · linarith only [h0, h5390, h5780, h5800, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h5800, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

end R2N4
