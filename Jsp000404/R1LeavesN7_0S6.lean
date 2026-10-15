import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7130000 in
set_option maxHeartbeats 7130000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  have h10 := hg10
  rcases m.htr 1 2 4 (by decide) (by decide) with h11 | h11
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s11 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3073 | h3073
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3074 | h3074
      · linarith only [h10, h11, h3074, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3076 | h3076
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3077 | h3077
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3078 | h3078
            · linarith only [h0, h3074, h3076, h3078, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3080 | h3080
              · linarith only [h0, h10, h11, h3080, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h10, h11, h3076, h3078, h3080, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h10, h11, h3076, h3077, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3084 | h3084
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3085 | h3085
            · linarith only [h0, h10, h11, h3085, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3087 | h3087
              · linarith only [h0, h10, h11, h3076, h3085, h3087, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3089 | h3089
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3090 | h3090
                  · rcases h1bigk with h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c | h3091c
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      rcases p3091_3 (m.d 0 1) (by simp) with h3093 | h3093
                      · rcases p3091_3 (m.d 1 2) (by simp) with h3094 | h3094
                        · linarith only [h3094, hlam, p3091_0]
                        · rcases p3091_3 (m.d 1 3) (by simp) with h3096 | h3096
                          · linarith only [h1, h3096, hlam]
                          · rcases p3091_3 (m.d 1 4) (by simp) with h3098 | h3098
                            · linarith only [h2, h3098, hlam]
                            · linarith only [h11, h3098, hlam]
                      · linarith only [h3093, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      rcases p3091_3 (m.d 0 1) (by simp) with h3102 | h3102
                      · rcases p3091_3 (m.d 1 2) (by simp) with h3103 | h3103
                        · linarith only [h0, h3103, hlam]
                        · linarith only [h10, h3103, hlam]
                      · linarith only [h3102, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      rcases p3091_3 (m.d 0 1) (by simp) with h3107 | h3107
                      · rcases p3091_3 (m.d 1 2) (by simp) with h3108 | h3108
                        · linarith only [h0, h3108, hlam]
                        · rcases p3091_3 (m.d 1 3) (by simp) with h3110 | h3110
                          · linarith only [h1, h3110, hlam]
                          · rcases p3091_3 (m.d 1 4) (by simp) with h3112 | h3112
                            · linarith only [h3112, hlam, p3091_0]
                            · rcases p3091_3 (m.d 1 5) (by simp) with h3114 | h3114
                              · linarith only [h3, h3114, hlam]
                              · rcases h1emax with h3116 | h3116 | h3116 | h3116 | h3116
                                · linarith only [h0, h11, h3085, h3116, h4, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h2bigk with h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c | h3118c
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    rcases p3118_3 (m.d 0 2) (by simp) with h3120 | h3120
                                    · rcases p3118_3 (m.d 1 2) (by simp) with h3121 | h3121
                                      · linarith only [h0, h3121, hlam]
                                      · rcases p3118_3 (m.d 2 3) (by simp) with h3123 | h3123
                                        · linarith only [h3123, h4, hlam]
                                        · rcases p3118_3 (m.d 2 4) (by simp) with h3125 | h3125
                                          · linarith only [h3125, h5, hlam]
                                          · linarith only [h11, h3125, hlam]
                                    · linarith only [h0, h3120, hlam]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h11, h3073, h3085, h3087, h4, h7, hlam, p3118_2]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h0, h11, h3073, h3087, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h11, h3073, h3085, h4, h7, hlam, p3118_2]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h0, hlam, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h11, h3085, h4, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h11, hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h11, h3085, h4, h7, hc02, hc25, hlam, hphi, ht0b, ht5b, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h4, hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h10, hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h3085, hlam, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h3087, hlam, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h5, hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h0, h10, h3085, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    rcases p3118_3 (m.d 0 2) (by simp) with h3144 | h3144
                                    · rcases p3118_3 (m.d 1 2) (by simp) with h3145 | h3145
                                      · linarith only [h11, h3145, hlam]
                                      · linarith only [h10, h3145, hlam]
                                    · linarith only [h3144, h4, hlam]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    rcases p3118_3 (m.d 0 2) (by simp) with h3150 | h3150
                                    · rcases p3118_3 (m.d 1 2) (by simp) with h3151 | h3151
                                      · linarith only [h11, h3151, hlam]
                                      · linarith only [h3073, h3151, hlam]
                                    · linarith only [h3150, h6, hlam]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h6, hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h3073, hlam, p3118_0]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h0, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [h3089, hlam, p3118_1]
                                  · have p3118_0 := h3118c.1
                                    have p3118_1 := h3118c.2.1
                                    have p3118_2 := h3118c.2.2.1
                                    have p3118_3 := h3118c.2.2.2
                                    linarith only [hlam, p3118_0]
                                · rcases h2bigk with h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c | h3160c
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    rcases p3160_3 (m.d 0 2) (by simp) with h3162 | h3162
                                    · rcases p3160_3 (m.d 1 2) (by simp) with h3163 | h3163
                                      · linarith only [h0, h3163, hlam]
                                      · rcases p3160_3 (m.d 2 3) (by simp) with h3165 | h3165
                                        · linarith only [h3165, h4, hlam]
                                        · rcases p3160_3 (m.d 2 4) (by simp) with h3167 | h3167
                                          · linarith only [h3167, h5, hlam]
                                          · linarith only [h11, h3167, hlam]
                                    · linarith only [h0, h3162, hlam]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h10, h11, h3085, h4, h7, hlam, p3160_2]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h0, h11, h3073, hc01, hc25, hlam, hphi, ht0b, ht5b, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h11, h3073, h5, hlam, p3160_2]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h0, hlam, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h0, h11, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h11, hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h0, h11, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h4, hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h10, hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h3085, hlam, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h3087, hlam, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h5, hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    rcases p3160_3 (m.d 0 2) (by simp) with h3186 | h3186
                                    · rcases p3160_3 (m.d 1 2) (by simp) with h3187 | h3187
                                      · linarith only [h11, h3187, hlam]
                                      · linarith only [h10, h3187, hlam]
                                    · linarith only [h3186, h4, hlam]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    rcases p3160_3 (m.d 0 2) (by simp) with h3192 | h3192
                                    · rcases p3160_3 (m.d 1 2) (by simp) with h3193 | h3193
                                      · linarith only [h11, h3193, hlam]
                                      · linarith only [h3073, h3193, hlam]
                                    · linarith only [h3192, h6, hlam]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h6, hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h3073, hlam, p3160_0]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h0, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [h3089, hlam, p3160_1]
                                  · have p3160_0 := h3160c.1
                                    have p3160_1 := h3160c.2.1
                                    have p3160_2 := h3160c.2.2.1
                                    have p3160_3 := h3160c.2.2.2
                                    linarith only [hlam, p3160_0]
                                · rcases h2bigk with h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c | h3202c
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    rcases p3202_3 (m.d 0 2) (by simp) with h3204 | h3204
                                    · rcases p3202_3 (m.d 1 2) (by simp) with h3205 | h3205
                                      · linarith only [h0, h3205, hlam]
                                      · rcases p3202_3 (m.d 2 3) (by simp) with h3207 | h3207
                                        · linarith only [h3207, h4, hlam]
                                        · rcases p3202_3 (m.d 2 4) (by simp) with h3209 | h3209
                                          · linarith only [h3209, h5, hlam]
                                          · linarith only [h11, h3209, hlam]
                                    · linarith only [h0, h3204, hlam]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h10, h11, h3085, h4, h7, hlam, p3202_2]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h0, h11, h3073, hc01, hc25, hlam, hphi, ht0b, ht5b, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h11, h3073, h5, hlam, p3202_2]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h0, hlam, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h0, h11, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h11, hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h0, h11, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h4, hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h10, hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h3085, hlam, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h3087, hlam, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h5, hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    rcases p3202_3 (m.d 0 2) (by simp) with h3228 | h3228
                                    · rcases p3202_3 (m.d 1 2) (by simp) with h3229 | h3229
                                      · linarith only [h11, h3229, hlam]
                                      · linarith only [h10, h3229, hlam]
                                    · linarith only [h3228, h4, hlam]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    rcases p3202_3 (m.d 0 2) (by simp) with h3234 | h3234
                                    · rcases p3202_3 (m.d 1 2) (by simp) with h3235 | h3235
                                      · linarith only [h11, h3235, hlam]
                                      · linarith only [h3073, h3235, hlam]
                                    · linarith only [h3234, h6, hlam]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h6, hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h3073, hlam, p3202_0]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h0, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [h3089, hlam, p3202_1]
                                  · have p3202_0 := h3202c.1
                                    have p3202_1 := h3202c.2.1
                                    have p3202_2 := h3202c.2.2.1
                                    have p3202_3 := h3202c.2.2.2
                                    linarith only [hlam, p3202_0]
                                · rcases h2bigk with h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c | h3244c
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    rcases p3244_3 (m.d 0 2) (by simp) with h3246 | h3246
                                    · rcases p3244_3 (m.d 1 2) (by simp) with h3247 | h3247
                                      · linarith only [h0, h3247, hlam]
                                      · rcases p3244_3 (m.d 2 3) (by simp) with h3249 | h3249
                                        · linarith only [h3249, h4, hlam]
                                        · rcases p3244_3 (m.d 2 4) (by simp) with h3251 | h3251
                                          · linarith only [h3251, h5, hlam]
                                          · linarith only [h11, h3251, hlam]
                                    · linarith only [h0, h3246, hlam]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h10, h11, h3085, h4, h7, hlam, p3244_2]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h0, h11, h3073, hc01, hc25, hlam, hphi, ht0b, ht5b, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h11, h3073, h5, hlam, p3244_2]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h0, hlam, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h0, h11, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h11, hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h0, h11, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h4, hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h10, hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h3085, hlam, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h3087, hlam, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h5, hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    rcases p3244_3 (m.d 0 2) (by simp) with h3270 | h3270
                                    · rcases p3244_3 (m.d 1 2) (by simp) with h3271 | h3271
                                      · linarith only [h11, h3271, hlam]
                                      · linarith only [h10, h3271, hlam]
                                    · linarith only [h3270, h4, hlam]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    rcases p3244_3 (m.d 0 2) (by simp) with h3276 | h3276
                                    · rcases p3244_3 (m.d 1 2) (by simp) with h3277 | h3277
                                      · linarith only [h11, h3277, hlam]
                                      · linarith only [h3073, h3277, hlam]
                                    · linarith only [h3276, h6, hlam]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h6, hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h3073, hlam, p3244_0]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h0, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [h3089, hlam, p3244_1]
                                  · have p3244_0 := h3244c.1
                                    have p3244_1 := h3244c.2.1
                                    have p3244_2 := h3244c.2.2.1
                                    have p3244_3 := h3244c.2.2.2
                                    linarith only [hlam, p3244_0]
                      · linarith only [h3107, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      rcases p3091_3 (m.d 0 1) (by simp) with h3287 | h3287
                      · rcases p3091_3 (m.d 1 2) (by simp) with h3288 | h3288
                        · linarith only [h0, h3288, hlam]
                        · linarith only [h3073, h3288, hlam]
                      · linarith only [h3287, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h0, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h0, h10, h11, h3085, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3091_1]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h11, hlam, p3091_1]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h0, h11, h3085, h4, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p3091_1]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h1, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h10, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h3074, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h3076, hlam, p3091_1]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h2, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h2, h3073, hc01, hc25, hlam, hphi, ht0b, ht5b, p3091_1]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      rcases p3091_3 (m.d 0 1) (by simp) with h3304 | h3304
                      · rcases p3091_3 (m.d 1 2) (by simp) with h3305 | h3305
                        · linarith only [h11, h3305, hlam]
                        · linarith only [h10, h3305, hlam]
                      · linarith only [h1, h3304, hlam]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      rcases p3091_3 (m.d 0 1) (by simp) with h3310 | h3310
                      · rcases p3091_3 (m.d 1 2) (by simp) with h3311 | h3311
                        · linarith only [h11, h3311, hlam]
                        · linarith only [h3073, h3311, hlam]
                      · linarith only [h3, h3310, hlam]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h3, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h3073, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h0, h10, h11, h3073, h3085, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3091_1]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [h3084, hlam, p3091_0]
                    · have p3091_0 := h3091c.1
                      have p3091_1 := h3091c.2.1
                      have p3091_2 := h3091c.2.2.1
                      have p3091_3 := h3091c.2.2.2
                      linarith only [hlam, p3091_0]
                  · linarith only [h0, h10, h11, h3085, h3090, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h11, h3073, h3076, h3084, h3087, h3089, hc23, hc35, hlam, hphi]
          · linarith only [h11, h3073, h3084, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3323 | h3323
      · linarith only [h10, h11, h3323, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3325 | h3325
        · linarith only [h10, h3073, h3325, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3327 | h3327
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3328 | h3328
            · linarith only [h0, h10, h11, h3323, h3328, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3330 | h3330
              · linarith only [h10, h3073, h3325, h3330, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3332 | h3332
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3333 | h3333
                  · rcases h1bigk with h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c | h3334c
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      rcases p3334_3 (m.d 0 1) (by simp) with h3336 | h3336
                      · rcases p3334_3 (m.d 1 2) (by simp) with h3337 | h3337
                        · linarith only [h3337, hlam, p3334_0]
                        · rcases p3334_3 (m.d 1 3) (by simp) with h3339 | h3339
                          · linarith only [h1, h3339, hlam]
                          · rcases p3334_3 (m.d 1 4) (by simp) with h3341 | h3341
                            · linarith only [h2, h3341, hlam]
                            · linarith only [h11, h3341, hlam]
                      · linarith only [h3336, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      rcases p3334_3 (m.d 0 1) (by simp) with h3345 | h3345
                      · rcases p3334_3 (m.d 1 2) (by simp) with h3346 | h3346
                        · linarith only [h0, h3346, hlam]
                        · linarith only [h10, h3346, hlam]
                      · linarith only [h3345, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      rcases p3334_3 (m.d 0 1) (by simp) with h3350 | h3350
                      · rcases p3334_3 (m.d 1 2) (by simp) with h3351 | h3351
                        · linarith only [h0, h3351, hlam]
                        · rcases p3334_3 (m.d 1 3) (by simp) with h3353 | h3353
                          · linarith only [h1, h3353, hlam]
                          · rcases p3334_3 (m.d 1 4) (by simp) with h3355 | h3355
                            · linarith only [h3355, hlam, p3334_0]
                            · rcases p3334_3 (m.d 1 5) (by simp) with h3357 | h3357
                              · linarith only [h3, h3357, hlam]
                              · rcases h1emax with h3359 | h3359 | h3359 | h3359 | h3359
                                · linarith only [h0, h3073, h3328, h3332, h3359, h4, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h2bigk with h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c | h3361c
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    rcases p3361_3 (m.d 0 2) (by simp) with h3363 | h3363
                                    · rcases p3361_3 (m.d 1 2) (by simp) with h3364 | h3364
                                      · linarith only [h0, h3364, hlam]
                                      · rcases p3361_3 (m.d 2 3) (by simp) with h3366 | h3366
                                        · linarith only [h3366, h4, hlam]
                                        · rcases p3361_3 (m.d 2 4) (by simp) with h3368 | h3368
                                          · linarith only [h3368, h5, hlam]
                                          · linarith only [h11, h3368, hlam]
                                    · linarith only [h0, h3363, hlam]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h10, h3073, h3328, h3332, h4, h7, hlam, p3361_2]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h0, h10, h3073, h3332, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h0, h10, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h0, hlam, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h3073, h3328, h3332, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h11, hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h3073, hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h4, hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h10, hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h3328, hlam, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h3330, hlam, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h5, hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h0, h10, h3328, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    rcases p3361_3 (m.d 0 2) (by simp) with h3387 | h3387
                                    · rcases p3361_3 (m.d 1 2) (by simp) with h3388 | h3388
                                      · linarith only [h11, h3388, hlam]
                                      · linarith only [h10, h3388, hlam]
                                    · linarith only [h3387, h4, hlam]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h0, h10, h3073, h3328, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h6, hlam, p3361_0]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h10, h3330, hc23, hc35, hlam, hphi, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    rcases p3361_3 (m.d 0 2) (by simp) with h3396 | h3396
                                    · rcases p3361_3 (m.d 1 2) (by simp) with h3397 | h3397
                                      · linarith only [h3073, h3397, hlam]
                                      · linarith only [h10, h3397, hlam]
                                    · linarith only [h3396, h4, hlam]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [h3332, hlam, p3361_1]
                                  · have p3361_0 := h3361c.1
                                    have p3361_1 := h3361c.2.1
                                    have p3361_2 := h3361c.2.2.1
                                    have p3361_3 := h3361c.2.2.2
                                    linarith only [hlam, p3361_0]
                                · rcases h2bigk with h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    rcases p3403_3 (m.d 0 2) (by simp) with h3405 | h3405
                                    · rcases p3403_3 (m.d 1 2) (by simp) with h3406 | h3406
                                      · linarith only [h0, h3406, hlam]
                                      · rcases p3403_3 (m.d 2 3) (by simp) with h3408 | h3408
                                        · linarith only [h3408, h4, hlam]
                                        · rcases p3403_3 (m.d 2 4) (by simp) with h3410 | h3410
                                          · linarith only [h3410, h5, hlam]
                                          · linarith only [h11, h3410, hlam]
                                    · linarith only [h0, h3405, hlam]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h10, h11, h3328, h4, h7, hlam, p3403_2]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h10, h11, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h0, h10, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h0, hlam, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h3073, h3327, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3334_1, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h11, hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h3073, hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h4, hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h10, hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h3328, hlam, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h3330, hlam, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h5, hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    rcases p3403_3 (m.d 0 2) (by simp) with h3429 | h3429
                                    · rcases p3403_3 (m.d 1 2) (by simp) with h3430 | h3430
                                      · linarith only [h11, h3430, hlam]
                                      · linarith only [h10, h3430, hlam]
                                    · linarith only [h3429, h4, hlam]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h0, h10, h3073, h3328, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h6, hlam, p3403_0]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h0, h10, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    rcases p3403_3 (m.d 0 2) (by simp) with h3438 | h3438
                                    · rcases p3403_3 (m.d 1 2) (by simp) with h3439 | h3439
                                      · linarith only [h3073, h3439, hlam]
                                      · linarith only [h10, h3439, hlam]
                                    · linarith only [h3438, h4, hlam]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [h3332, hlam, p3403_1]
                                  · have p3403_0 := h3403c.1
                                    have p3403_1 := h3403c.2.1
                                    have p3403_2 := h3403c.2.2.1
                                    have p3403_3 := h3403c.2.2.2
                                    linarith only [hlam, p3403_0]
                                · rcases h2bigk with h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c | h3445c
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    rcases p3445_3 (m.d 0 2) (by simp) with h3447 | h3447
                                    · rcases p3445_3 (m.d 1 2) (by simp) with h3448 | h3448
                                      · linarith only [h0, h3448, hlam]
                                      · rcases p3445_3 (m.d 2 3) (by simp) with h3450 | h3450
                                        · linarith only [h3450, h4, hlam]
                                        · rcases p3445_3 (m.d 2 4) (by simp) with h3452 | h3452
                                          · linarith only [h3452, h5, hlam]
                                          · linarith only [h11, h3452, hlam]
                                    · linarith only [h0, h3447, hlam]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h10, h11, h3328, h4, h7, hlam, p3445_2]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h10, h11, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h0, h10, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h0, hlam, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h3073, h3327, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3334_1, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h11, hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h3073, hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h4, hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h10, hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h3328, hlam, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h3330, hlam, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h5, hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    rcases p3445_3 (m.d 0 2) (by simp) with h3471 | h3471
                                    · rcases p3445_3 (m.d 1 2) (by simp) with h3472 | h3472
                                      · linarith only [h11, h3472, hlam]
                                      · linarith only [h10, h3472, hlam]
                                    · linarith only [h3471, h4, hlam]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h0, h10, h3073, h3328, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h6, hlam, p3445_0]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h0, h10, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    rcases p3445_3 (m.d 0 2) (by simp) with h3480 | h3480
                                    · rcases p3445_3 (m.d 1 2) (by simp) with h3481 | h3481
                                      · linarith only [h3073, h3481, hlam]
                                      · linarith only [h10, h3481, hlam]
                                    · linarith only [h3480, h4, hlam]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [h3332, hlam, p3445_1]
                                  · have p3445_0 := h3445c.1
                                    have p3445_1 := h3445c.2.1
                                    have p3445_2 := h3445c.2.2.1
                                    have p3445_3 := h3445c.2.2.2
                                    linarith only [hlam, p3445_0]
                                · rcases h2bigk with h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c | h3487c
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    rcases p3487_3 (m.d 0 2) (by simp) with h3489 | h3489
                                    · rcases p3487_3 (m.d 1 2) (by simp) with h3490 | h3490
                                      · linarith only [h0, h3490, hlam]
                                      · rcases p3487_3 (m.d 2 3) (by simp) with h3492 | h3492
                                        · linarith only [h3492, h4, hlam]
                                        · rcases p3487_3 (m.d 2 4) (by simp) with h3494 | h3494
                                          · linarith only [h3494, h5, hlam]
                                          · linarith only [h11, h3494, hlam]
                                    · linarith only [h0, h3489, hlam]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h10, h11, h3328, h4, h7, hlam, p3487_2]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h10, h11, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h0, h10, h3073, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h0, hlam, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h3073, h3327, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3334_1, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h11, hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h3073, hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h4, hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h10, hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h3328, hlam, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h3330, hlam, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h5, hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h0, h10, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    rcases p3487_3 (m.d 0 2) (by simp) with h3513 | h3513
                                    · rcases p3487_3 (m.d 1 2) (by simp) with h3514 | h3514
                                      · linarith only [h11, h3514, hlam]
                                      · linarith only [h10, h3514, hlam]
                                    · linarith only [h3513, h4, hlam]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h0, h10, h3073, h3328, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h6, hlam, p3487_0]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h0, h10, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    rcases p3487_3 (m.d 0 2) (by simp) with h3522 | h3522
                                    · rcases p3487_3 (m.d 1 2) (by simp) with h3523 | h3523
                                      · linarith only [h3073, h3523, hlam]
                                      · linarith only [h10, h3523, hlam]
                                    · linarith only [h3522, h4, hlam]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [h3332, hlam, p3487_1]
                                  · have p3487_0 := h3487c.1
                                    have p3487_1 := h3487c.2.1
                                    have p3487_2 := h3487c.2.2.1
                                    have p3487_3 := h3487c.2.2.2
                                    linarith only [hlam, p3487_0]
                      · linarith only [h3350, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      rcases p3334_3 (m.d 0 1) (by simp) with h3530 | h3530
                      · rcases p3334_3 (m.d 1 2) (by simp) with h3531 | h3531
                        · linarith only [h0, h3531, hlam]
                        · rcases p3334_3 (m.d 1 3) (by simp) with h3533 | h3533
                          · linarith only [h1, h3533, hlam]
                          · rcases p3334_3 (m.d 1 4) (by simp) with h3535 | h3535
                            · linarith only [h2, h3535, hlam]
                            · linarith only [h3327, h3535, hlam]
                      · linarith only [h3530, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h0, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h0, h10, h11, h3328, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3334_1]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h11, hlam, p3334_1]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h3073, hlam, p3334_1]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h1, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h10, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h3323, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h3325, hlam, p3334_1]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h2, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h10, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3334_1]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      rcases p3334_3 (m.d 0 1) (by simp) with h3551 | h3551
                      · rcases p3334_3 (m.d 1 2) (by simp) with h3552 | h3552
                        · linarith only [h11, h3552, hlam]
                        · linarith only [h10, h3552, hlam]
                      · linarith only [h1, h3551, hlam]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h0, h10, h11, h3073, h3328, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3334_1]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h3, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3334_1]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      rcases p3334_3 (m.d 0 1) (by simp) with h3560 | h3560
                      · rcases p3334_3 (m.d 1 2) (by simp) with h3561 | h3561
                        · linarith only [h3073, h3561, hlam]
                        · linarith only [h10, h3561, hlam]
                      · linarith only [h1, h3560, hlam]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [h3327, hlam, p3334_0]
                    · have p3334_0 := h3334c.1
                      have p3334_1 := h3334c.2.1
                      have p3334_2 := h3334c.2.2.1
                      have p3334_3 := h3334c.2.2.2
                      linarith only [hlam, p3334_0]
                  · linarith only [h0, h10, h11, h3328, h3333, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h11, h3327, h3332, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3569 | h3569
            · linarith only [h0, h10, h11, h3569, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3571 | h3571
              · linarith only [h0, h10, h11, h3327, h3571, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3573 | h3573
                · linarith only [h0, h10, h11, h3327, h3569, h3573, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h10, h11, h3573, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

end R2N4
