import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S3
import Jsp000404.R1LeavesN7_11S4
import Jsp000404.R1LeavesN7_11S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2031 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2186 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h2187 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 4 5 (by decide) (by decide) with h3020 | h3020
  · linarith only [h2186, h2187, h3020, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h3022 | h3022
    · rcases m.htr 2 3 5 (by decide) (by decide) with h3023 | h3023
      · linarith only [h0, h2186, h2187, h3, h3023, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3025 | h3025
        · linarith only [h0, h3, h3020, h3022, h3023, h3025, h7, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h3027 | h3027
          · linarith only [h0, h2186, h3, h3023, h3025, h3027, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases h2bigk with h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c | h3029c
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h3, h3023, h3027, h6, h8, h9, hlam, p3029_2]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              rcases p3029_3 (m.d 0 2) (by simp) with h3032 | h3032
              · rcases p3029_3 (m.d 1 2) (by simp) with h3033 | h3033
                · linarith only [h0, h3033, hlam]
                · rcases p3029_3 (m.d 2 3) (by simp) with h3035 | h3035
                  · linarith only [h3035, hlam, p3029_0]
                  · rcases p3029_3 (m.d 2 4) (by simp) with h3037 | h3037
                    · linarith only [h3037, h4, hlam]
                    · rcases p3029_3 (m.d 2 5) (by simp) with h3039 | h3039
                      · linarith only [h3039, h5, hlam]
                      · linarith only [h3023, h3039, hlam]
              · linarith only [h3032, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              rcases p3029_3 (m.d 0 2) (by simp) with h3043 | h3043
              · rcases p3029_3 (m.d 1 2) (by simp) with h3044 | h3044
                · linarith only [h0, h3044, hlam]
                · rcases p3029_3 (m.d 2 3) (by simp) with h3046 | h3046
                  · linarith only [h3, h3046, hlam]
                  · linarith only [h3022, h3046, hlam]
              · linarith only [h3043, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              rcases p3029_3 (m.d 0 2) (by simp) with h3050 | h3050
              · rcases p3029_3 (m.d 1 2) (by simp) with h3051 | h3051
                · linarith only [h0, h3051, hlam]
                · rcases p3029_3 (m.d 2 3) (by simp) with h3053 | h3053
                  · linarith only [h3, h3053, hlam]
                  · rcases p3029_3 (m.d 2 4) (by simp) with h3055 | h3055
                    · linarith only [h3055, h4, hlam]
                    · rcases p3029_3 (m.d 2 5) (by simp) with h3057 | h3057
                      · linarith only [h3057, hlam, p3029_0]
                      · rcases h3bigk with h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c | h3059c
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          rcases p3059_3 (m.d 0 3) (by simp) with h3061 | h3061
                          · rcases p3059_3 (m.d 1 3) (by simp) with h3062 | h3062
                            · linarith only [h1, h3062, hlam]
                            · rcases p3059_3 (m.d 2 3) (by simp) with h3064 | h3064
                              · linarith only [h3, h3064, hlam]
                              · linarith only [h3064, h9, hlam]
                          · linarith only [h1, h3061, hlam]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          rcases p3059_3 (m.d 0 3) (by simp) with h3068 | h3068
                          · rcases p3059_3 (m.d 1 3) (by simp) with h3069 | h3069
                            · linarith only [h1, h3069, hlam]
                            · rcases p3059_3 (m.d 2 3) (by simp) with h3071 | h3071
                              · linarith only [h3, h3071, hlam]
                              · rcases p3059_3 (m.d 3 4) (by simp) with h3073 | h3073
                                · linarith only [h3073, h6, hlam]
                                · rcases p3059_3 (m.d 3 5) (by simp) with h3075 | h3075
                                  · linarith only [h3075, h7, hlam]
                                  · linarith only [h3023, h3075, hlam]
                          · linarith only [h3, h3068, hlam]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2186, h3023, h3027, h6, h8, h9, hlam, p3059_2]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h0, h3, h3023, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h1, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h9, hlam, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3023, h3027, h9, hc34, hc45, hlam, hphi, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2187, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3023, hc13, hc35, hlam, hphi, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h0, h3, h3023, h3027, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3023, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h6, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h2186, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3022, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h3027, hlam, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h7, hlam, p3059_0]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h0, h2186, h3, h3027, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [h0, h3, h3027, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3059_1]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          rcases p3059_3 (m.d 0 3) (by simp) with h3099 | h3099
                          · rcases p3059_3 (m.d 1 3) (by simp) with h3100 | h3100
                            · linarith only [h2187, h3100, hlam]
                            · linarith only [h2186, h3100, hlam]
                          · linarith only [h3099, h6, hlam]
                        · have p3059_0 := h3059c.1
                          have p3059_1 := h3059c.2.1
                          have p3059_2 := h3059c.2.2.1
                          have p3059_3 := h3059c.2.2.2
                          linarith only [hlam, p3059_0]
              · linarith only [h3050, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h0, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h9, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h0, h3, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3029_1]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h2031, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h3, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h0, h3, h3023, h3027, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3029_1]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h0, h3, h3022, h3023, h3027, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3029_1]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h3023, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h4, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h0, h3, h3022, h3023, h3027, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3029_1]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h3022, hlam, p3029_1]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h3025, hlam, p3029_1]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h5, hlam, p3029_0]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              rcases p3029_3 (m.d 0 2) (by simp) with h3122 | h3122
              · rcases p3029_3 (m.d 1 2) (by simp) with h3123 | h3123
                · linarith only [h3123, hlam, p3029_0]
                · rcases p3029_3 (m.d 2 3) (by simp) with h3125 | h3125
                  · linarith only [h3023, h3125, hlam]
                  · linarith only [h3125, h9, hlam]
              · linarith only [h0, h3122, hlam]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [h0, h3, h3023, h3027, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3029_1]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              rcases p3029_3 (m.d 0 2) (by simp) with h3130 | h3130
              · rcases p3029_3 (m.d 1 2) (by simp) with h3131 | h3131
                · linarith only [h2031, h3131, hlam]
                · rcases p3029_3 (m.d 2 3) (by simp) with h3133 | h3133
                  · linarith only [h3023, h3133, hlam]
                  · linarith only [h3022, h3133, hlam]
              · linarith only [h3130, h4, hlam]
            · have p3029_0 := h3029c.1
              have p3029_1 := h3029c.2.1
              have p3029_2 := h3029c.2.2.1
              have p3029_3 := h3029c.2.2.2
              linarith only [hlam, p3029_0]
    · linarith only [h1, h2186, h3022, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2031 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2186 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h2187 | h2187
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2031 h2186 h2187
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2031 h2186 h2187

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2031 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2186 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h3139 | h3139
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3140 | h3140
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3141 | h3141
      · linarith only [h0, h2186, h3, h3139, h3141, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3143 | h3143
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3144 | h3144
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3145 | h3145
            · rcases h2bigk with h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h3, h3141, h6, h9, hlam, p3146_2]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                rcases p3146_3 (m.d 0 2) (by simp) with h3149 | h3149
                · rcases p3146_3 (m.d 1 2) (by simp) with h3150 | h3150
                  · linarith only [h0, h3150, hlam]
                  · rcases p3146_3 (m.d 2 3) (by simp) with h3152 | h3152
                    · linarith only [h3152, hlam, p3146_0]
                    · rcases p3146_3 (m.d 2 4) (by simp) with h3154 | h3154
                      · linarith only [h3154, h4, hlam]
                      · linarith only [h3141, h3154, hlam]
                · linarith only [h3149, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                rcases p3146_3 (m.d 0 2) (by simp) with h3158 | h3158
                · rcases p3146_3 (m.d 1 2) (by simp) with h3159 | h3159
                  · linarith only [h0, h3159, hlam]
                  · rcases p3146_3 (m.d 2 3) (by simp) with h3161 | h3161
                    · linarith only [h3, h3161, hlam]
                    · rcases p3146_3 (m.d 2 4) (by simp) with h3163 | h3163
                      · linarith only [h3163, hlam, p3146_0]
                      · rcases p3146_3 (m.d 2 5) (by simp) with h3165 | h3165
                        · linarith only [h3165, h5, hlam]
                        · rcases h3bigk with h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c | h3167c
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            rcases p3167_3 (m.d 0 3) (by simp) with h3169 | h3169
                            · rcases p3167_3 (m.d 1 3) (by simp) with h3170 | h3170
                              · linarith only [h1, h3170, hlam]
                              · rcases p3167_3 (m.d 2 3) (by simp) with h3172 | h3172
                                · linarith only [h3, h3172, hlam]
                                · linarith only [h3172, h9, hlam]
                            · linarith only [h1, h3169, hlam]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            rcases p3167_3 (m.d 0 3) (by simp) with h3176 | h3176
                            · rcases p3167_3 (m.d 1 3) (by simp) with h3177 | h3177
                              · linarith only [h1, h3177, hlam]
                              · rcases p3167_3 (m.d 2 3) (by simp) with h3179 | h3179
                                · linarith only [h3, h3179, hlam]
                                · rcases p3167_3 (m.d 3 4) (by simp) with h3181 | h3181
                                  · linarith only [h3181, h6, hlam]
                                  · linarith only [h3141, h3181, hlam]
                            · linarith only [h3, h3176, hlam]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, h2031, h3, h3141, h3143, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h3139, h3141, h6, h9, hlam, p3167_2]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h1, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h9, hlam, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h2186, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, h3141, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p3146_1, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h3, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, h3141, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3146_1, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h3141, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h3141, h6, hc03, hc35, hlam, hphi, ht0b, ht5b, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h6, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, h3, h3139, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h0, h3, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3167_1]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            rcases p3167_3 (m.d 0 3) (by simp) with h3201 | h3201
                            · rcases p3167_3 (m.d 1 3) (by simp) with h3202 | h3202
                              · linarith only [h2186, h3202, hlam]
                              · linarith only [h3139, h3202, hlam]
                            · linarith only [h3201, h7, hlam]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h7, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h3139, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h3143, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [h3145, hlam, p3167_0]
                          · have p3167_0 := h3167c.1
                            have p3167_1 := h3167c.2.1
                            have p3167_2 := h3167c.2.2.1
                            have p3167_3 := h3167c.2.2.2
                            linarith only [hlam, p3167_0]
                · linarith only [h3158, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                rcases p3146_3 (m.d 0 2) (by simp) with h3212 | h3212
                · rcases p3146_3 (m.d 1 2) (by simp) with h3213 | h3213
                  · linarith only [h0, h3213, hlam]
                  · rcases p3146_3 (m.d 2 3) (by simp) with h3215 | h3215
                    · linarith only [h3, h3215, hlam]
                    · linarith only [h3143, h3215, hlam]
                · linarith only [h3212, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h0, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h9, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h0, h2031, h3, h3143, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3146_1]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h2031, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h3, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h0, h3, h3141, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3146_1]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h3141, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h0, h3, h3141, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p3146_1]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h4, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                rcases p3146_3 (m.d 0 2) (by simp) with h3230 | h3230
                · rcases p3146_3 (m.d 1 2) (by simp) with h3231 | h3231
                  · linarith only [h3231, hlam, p3146_0]
                  · rcases p3146_3 (m.d 2 3) (by simp) with h3233 | h3233
                    · linarith only [h3141, h3233, hlam]
                    · linarith only [h3233, h9, hlam]
                · linarith only [h0, h3230, hlam]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3146_1]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h0, h2031, h3, h3141, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3146_1]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h5, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h0, h3, h3141, h3143, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3146_1]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h3143, hlam, p3146_1]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [h3144, hlam, p3146_0]
              · have p3146_0 := h3146c.1
                have p3146_1 := h3146c.2.1
                have p3146_2 := h3146c.2.2.1
                have p3146_3 := h3146c.2.2.2
                linarith only [hlam, p3146_0]
            · linarith only [h0, h3, h3141, h3145, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h3139, h3140, h3141, h3144, h9, hlam]
        · linarith only [h3139, h3143, h9, hlam]
    · linarith only [h2186, h3139, h3140, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3249 | h3249
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3250 | h3250
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3251 | h3251
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3252 | h3252
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3253 | h3253
            · rcases h2bigk with h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c | h3254c
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3, h3139, h3250, h3253, h9, hlam, p3254_2]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3139, h3250, h3253, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3254_1]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                rcases p3254_3 (m.d 0 2) (by simp) with h3258 | h3258
                · rcases p3254_3 (m.d 1 2) (by simp) with h3259 | h3259
                  · linarith only [h0, h3259, hlam]
                  · rcases p3254_3 (m.d 2 3) (by simp) with h3261 | h3261
                    · linarith only [h3, h3261, hlam]
                    · linarith only [h3250, h3261, hlam]
                · linarith only [h3258, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                rcases p3254_3 (m.d 0 2) (by simp) with h3265 | h3265
                · rcases p3254_3 (m.d 1 2) (by simp) with h3266 | h3266
                  · linarith only [h0, h3266, hlam]
                  · rcases p3254_3 (m.d 2 3) (by simp) with h3268 | h3268
                    · linarith only [h3, h3268, hlam]
                    · linarith only [h3251, h3268, hlam]
                · linarith only [h3265, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h0, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h9, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3139, h3251, h3252, h9, hlam, p3254_1]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h2031, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                rcases p3254_3 (m.d 0 2) (by simp) with h3278 | h3278
                · rcases p3254_3 (m.d 1 2) (by simp) with h3279 | h3279
                  · linarith only [h3279, hlam, p3254_0]
                  · rcases p3254_3 (m.d 2 3) (by simp) with h3281 | h3281
                    · rcases p3254_3 (m.d 2 4) (by simp) with h3282 | h3282
                      · linarith only [h3250, h3282, hlam]
                      · linarith only [h3139, h3251, h3252, h3282, h9, hlam]
                    · linarith only [h3281, hlam, p3254_0]
                · linarith only [h0, h3278, hlam]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3139, h3251, h3252, h9, hc12, hc23, hlam, hphi, p3254_1]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h0, h3, h3139, h3251, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3254_1]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h4, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                rcases p3254_3 (m.d 0 2) (by simp) with h3291 | h3291
                · rcases p3254_3 (m.d 1 2) (by simp) with h3292 | h3292
                  · linarith only [h3292, hlam, p3254_0]
                  · rcases p3254_3 (m.d 2 3) (by simp) with h3294 | h3294
                    · rcases p3254_3 (m.d 2 4) (by simp) with h3295 | h3295
                      · rcases p3254_3 (m.d 2 5) (by simp) with h3296 | h3296
                        · linarith only [h3252, h3296, hlam]
                        · linarith only [h2031, h3296, hlam]
                      · linarith only [h3295, hlam, p3254_0]
                    · linarith only [h3294, h9, hlam]
                · linarith only [h0, h3291, hlam]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3250, hlam, p3254_1]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3139, h3251, h9, hc12, hc24, hlam, hphi, p3254_1]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h5, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                rcases p3254_3 (m.d 0 2) (by simp) with h3306 | h3306
                · rcases p3254_3 (m.d 1 2) (by simp) with h3307 | h3307
                  · linarith only [h3307, hlam, p3254_0]
                  · rcases p3254_3 (m.d 2 3) (by simp) with h3309 | h3309
                    · rcases p3254_3 (m.d 2 4) (by simp) with h3310 | h3310
                      · rcases p3254_3 (m.d 2 5) (by simp) with h3311 | h3311
                        · rcases h3bigk with h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c | h3312c
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            rcases p3312_3 (m.d 0 3) (by simp) with h3314 | h3314
                            · rcases p3312_3 (m.d 1 3) (by simp) with h3315 | h3315
                              · linarith only [h1, h3315, hlam]
                              · rcases p3312_3 (m.d 2 3) (by simp) with h3317 | h3317
                                · linarith only [h3, h3317, hlam]
                                · linarith only [h3317, h9, hlam]
                            · linarith only [h1, h3314, hlam]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h0, h3, h3139, h3250, h3253, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3312_1]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            rcases p3312_3 (m.d 0 3) (by simp) with h3322 | h3322
                            · rcases p3312_3 (m.d 1 3) (by simp) with h3323 | h3323
                              · linarith only [h1, h3323, hlam]
                              · rcases p3312_3 (m.d 2 3) (by simp) with h3325 | h3325
                                · linarith only [h3, h3325, hlam]
                                · linarith only [h3250, h3325, hlam]
                            · linarith only [h3322, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            rcases p3312_3 (m.d 0 3) (by simp) with h3329 | h3329
                            · rcases p3312_3 (m.d 1 3) (by simp) with h3330 | h3330
                              · linarith only [h1, h3330, hlam]
                              · rcases p3312_3 (m.d 2 3) (by simp) with h3332 | h3332
                                · linarith only [h3, h3332, hlam]
                                · linarith only [h3251, h3332, hlam]
                            · linarith only [h3329, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h1, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h9, hlam, p3312_1]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h2186, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h3139, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h3, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            rcases p3312_3 (m.d 0 3) (by simp) with h3342 | h3342
                            · rcases p3312_3 (m.d 1 3) (by simp) with h3343 | h3343
                              · linarith only [h3343, h9, hlam]
                              · rcases p3312_3 (m.d 2 3) (by simp) with h3345 | h3345
                                · rcases p3312_3 (m.d 3 4) (by simp) with h3346 | h3346
                                  · linarith only [h3250, h3346, hlam]
                                  · linarith only [h2186, h3346, hlam]
                                · linarith only [h3345, h9, hlam]
                            · linarith only [h1, h3342, hlam]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h3139, h3253, h9, hc12, hc23, hlam, hphi, p3312_1]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h0, h3, h3139, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3312_1]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h6, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h0, h3, h3250, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3312_1]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h3250, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h0, h3, h3139, h3250, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3312_1]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h7, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h0, h3, h3251, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3312_1]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h3251, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [h3253, hlam, p3312_0]
                          · have p3312_0 := h3312c.1
                            have p3312_1 := h3312c.2.1
                            have p3312_2 := h3312c.2.2.1
                            have p3312_3 := h3312c.2.2.2
                            linarith only [hlam, p3312_0]
                        · linarith only [h3311, hlam, p3254_0]
                      · linarith only [h2186, h3250, h3310, h9, hlam]
                    · linarith only [h3309, h9, hlam]
                · linarith only [h0, h3306, hlam]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3251, hlam, p3254_1]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [h3252, hlam, p3254_0]
              · have p3254_0 := h3254c.1
                have p3254_1 := h3254c.2.1
                have p3254_2 := h3254c.2.2.1
                have p3254_3 := h3254c.2.2.2
                linarith only [hlam, p3254_0]
            · linarith only [h2186, h3249, h3253, hlam]
          · linarith only [h0, h2186, h3, h3249, h3250, h3252, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h2186, h3, h3249, h3250, h3251, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3374 | h3374
        · linarith only [h3139, h3250, h3374, h9, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3376 | h3376
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3377 | h3377
            · rcases h2bigk with h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c | h3378c
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h3, h3374, h3377, h6, h9, hlam, p3378_2]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                rcases p3378_3 (m.d 0 2) (by simp) with h3381 | h3381
                · rcases p3378_3 (m.d 1 2) (by simp) with h3382 | h3382
                  · linarith only [h0, h3382, hlam]
                  · rcases p3378_3 (m.d 2 3) (by simp) with h3384 | h3384
                    · linarith only [h3384, hlam, p3378_0]
                    · rcases p3378_3 (m.d 2 4) (by simp) with h3386 | h3386
                      · linarith only [h3386, h4, hlam]
                      · linarith only [h3250, h3386, hlam]
                · linarith only [h3381, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                rcases p3378_3 (m.d 0 2) (by simp) with h3390 | h3390
                · rcases p3378_3 (m.d 1 2) (by simp) with h3391 | h3391
                  · linarith only [h0, h3391, hlam]
                  · rcases p3378_3 (m.d 2 3) (by simp) with h3393 | h3393
                    · linarith only [h3, h3393, hlam]
                    · rcases p3378_3 (m.d 2 4) (by simp) with h3395 | h3395
                      · linarith only [h3395, hlam, p3378_0]
                      · rcases p3378_3 (m.d 2 5) (by simp) with h3397 | h3397
                        · linarith only [h3397, h5, hlam]
                        · rcases h3bigk with h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c | h3399c
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            rcases p3399_3 (m.d 0 3) (by simp) with h3401 | h3401
                            · rcases p3399_3 (m.d 1 3) (by simp) with h3402 | h3402
                              · linarith only [h1, h3402, hlam]
                              · rcases p3399_3 (m.d 2 3) (by simp) with h3404 | h3404
                                · linarith only [h3, h3404, hlam]
                                · linarith only [h3404, h9, hlam]
                            · linarith only [h1, h3401, hlam]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            rcases p3399_3 (m.d 0 3) (by simp) with h3408 | h3408
                            · rcases p3399_3 (m.d 1 3) (by simp) with h3409 | h3409
                              · linarith only [h1, h3409, hlam]
                              · rcases p3399_3 (m.d 2 3) (by simp) with h3411 | h3411
                                · linarith only [h3, h3411, hlam]
                                · rcases p3399_3 (m.d 3 4) (by simp) with h3413 | h3413
                                  · linarith only [h3413, h6, hlam]
                                  · linarith only [h3250, h3413, hlam]
                            · linarith only [h3, h3408, hlam]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h0, h3, h3374, h3377, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3399_1]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h0, h3, h3374, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3399_1]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h1, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h9, hlam, p3399_1]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h2186, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h3139, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h3, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h3374, h3377, hc13, hc34, hlam, hphi, p3399_1]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h3250, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h3374, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h6, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            rcases p3399_3 (m.d 0 3) (by simp) with h3430 | h3430
                            · rcases p3399_3 (m.d 1 3) (by simp) with h3431 | h3431
                              · linarith only [h3431, hlam, p3399_0]
                              · rcases p3399_3 (m.d 2 3) (by simp) with h3433 | h3433
                                · linarith only [h3250, h3433, hlam]
                                · linarith only [h3433, h9, hlam]
                            · linarith only [h1, h3430, hlam]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h0, h3, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3399_1]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h0, h3, h3139, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3399_1]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h7, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            rcases p3399_3 (m.d 0 3) (by simp) with h3441 | h3441
                            · rcases p3399_3 (m.d 1 3) (by simp) with h3442 | h3442
                              · linarith only [h3442, hlam, p3399_0]
                              · rcases p3399_3 (m.d 2 3) (by simp) with h3444 | h3444
                                · linarith only [h3374, h3444, hlam]
                                · linarith only [h3444, h9, hlam]
                            · linarith only [h1, h3441, hlam]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p3399_1]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [h3377, hlam, p3399_0]
                          · have p3399_0 := h3399c.1
                            have p3399_1 := h3399c.2.1
                            have p3399_2 := h3399c.2.2.1
                            have p3399_3 := h3399c.2.2.2
                            linarith only [hlam, p3399_0]
                · linarith only [h3390, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                rcases p3378_3 (m.d 0 2) (by simp) with h3452 | h3452
                · rcases p3378_3 (m.d 1 2) (by simp) with h3453 | h3453
                  · linarith only [h0, h3453, hlam]
                  · rcases p3378_3 (m.d 2 3) (by simp) with h3455 | h3455
                    · linarith only [h3, h3455, hlam]
                    · rcases p3378_3 (m.d 2 4) (by simp) with h3457 | h3457
                      · linarith only [h3457, h4, hlam]
                      · linarith only [h3376, h3457, hlam]
                · linarith only [h3452, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h0, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h9, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h0, h3, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3378_1]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h2031, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h3, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h0, h3, h3250, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3378_1]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h3250, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h3374, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h4, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                rcases p3378_3 (m.d 0 2) (by simp) with h3472 | h3472
                · rcases p3378_3 (m.d 1 2) (by simp) with h3473 | h3473
                  · linarith only [h3473, hlam, p3378_0]
                  · rcases p3378_3 (m.d 2 3) (by simp) with h3475 | h3475
                    · linarith only [h3250, h3475, hlam]
                    · linarith only [h3475, h9, hlam]
                · linarith only [h0, h3472, hlam]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3378_1]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h0, h3, h3250, h3374, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3378_1]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h5, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                rcases p3378_3 (m.d 0 2) (by simp) with h3483 | h3483
                · rcases p3378_3 (m.d 1 2) (by simp) with h3484 | h3484
                  · linarith only [h3484, hlam, p3378_0]
                  · rcases p3378_3 (m.d 2 3) (by simp) with h3486 | h3486
                    · linarith only [h3374, h3486, hlam]
                    · linarith only [h3486, h9, hlam]
                · linarith only [h0, h3483, hlam]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h9, hc12, hc25, hlam, hphi, p3378_1]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [h3376, hlam, p3378_0]
              · have p3378_0 := h3378c.1
                have p3378_1 := h3378c.2.1
                have p3378_2 := h3378c.2.2.1
                have p3378_3 := h3378c.2.2.2
                linarith only [hlam, p3378_0]
            · linarith only [h2186, h3249, h3377, hlam]
          · linarith only [h2186, h3249, h3250, h3376, h9, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3495 | h3495
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3496 | h3496
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3497 | h3497
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3498 | h3498
            · linarith only [h0, h3, h3249, h3495, h3498, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2186, h3, h3495, h3497, h3498, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3501 | h3501
            · linarith only [h3495, h3497, h3501, hlam]
            · rcases h2bigk with h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c | h3503c
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h2186, h3, h3495, h3497, h6, h8, h9, hlam, p3503_2]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h3139, h3496, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                rcases p3503_3 (m.d 0 2) (by simp) with h3507 | h3507
                · rcases p3503_3 (m.d 1 2) (by simp) with h3508 | h3508
                  · linarith only [h0, h3508, hlam]
                  · rcases p3503_3 (m.d 2 3) (by simp) with h3510 | h3510
                    · linarith only [h3, h3510, hlam]
                    · linarith only [h3495, h3510, hlam]
                · linarith only [h3507, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                rcases p3503_3 (m.d 0 2) (by simp) with h3514 | h3514
                · rcases p3503_3 (m.d 1 2) (by simp) with h3515 | h3515
                  · linarith only [h0, h3515, hlam]
                  · rcases p3503_3 (m.d 2 3) (by simp) with h3517 | h3517
                    · linarith only [h3, h3517, hlam]
                    · linarith only [h3496, h3517, hlam]
                · linarith only [h3514, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h0, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h9, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h2186, h3495, h9, hlam, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h2031, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h3, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                rcases p3503_3 (m.d 0 2) (by simp) with h3527 | h3527
                · rcases p3503_3 (m.d 1 2) (by simp) with h3528 | h3528
                  · linarith only [h3528, hlam, p3503_0]
                  · rcases p3503_3 (m.d 2 3) (by simp) with h3530 | h3530
                    · rcases p3503_3 (m.d 2 4) (by simp) with h3531 | h3531
                      · linarith only [h3495, h3531, hlam]
                      · linarith only [h2186, h3495, h3531, h9, hlam]
                    · linarith only [h3530, hlam, p3503_0]
                · linarith only [h0, h3527, hlam]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h2186, h3495, h9, hc12, hc23, hlam, hphi, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h0, h2031, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h4, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h3497, h6, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h3495, hlam, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h3497, hlam, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h5, hlam, p3503_0]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                rcases p3503_3 (m.d 0 2) (by simp) with h3545 | h3545
                · rcases p3503_3 (m.d 1 2) (by simp) with h3546 | h3546
                  · linarith only [h3546, hlam, p3503_0]
                  · rcases p3503_3 (m.d 2 3) (by simp) with h3548 | h3548
                    · rcases p3503_3 (m.d 2 4) (by simp) with h3549 | h3549
                      · linarith only [h3497, h3549, hlam]
                      · linarith only [h2186, h3495, h3549, h9, hlam]
                    · linarith only [h3548, h9, hlam]
                · linarith only [h0, h3545, hlam]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h3496, hlam, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [h2186, h3495, h9, hc12, hc25, hlam, hphi, p3503_1]
              · have p3503_0 := h3503c.1
                have p3503_1 := h3503c.2.1
                have p3503_2 := h3503c.2.2.1
                have p3503_3 := h3503c.2.2.2
                linarith only [hlam, p3503_0]
        · linarith only [h2186, h3495, h3496, h9, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3558 | h3558
        · linarith only [h0, h3, h3139, h3495, h3558, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3560 | h3560
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3561 | h3561
            · rcases h2bigk with h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c | h3562c
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h3, h3558, h7, h9, hlam, p3562_2]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                rcases p3562_3 (m.d 0 2) (by simp) with h3565 | h3565
                · rcases p3562_3 (m.d 1 2) (by simp) with h3566 | h3566
                  · linarith only [h0, h3566, hlam]
                  · rcases p3562_3 (m.d 2 3) (by simp) with h3568 | h3568
                    · linarith only [h3568, hlam, p3562_0]
                    · rcases p3562_3 (m.d 2 4) (by simp) with h3570 | h3570
                      · linarith only [h3570, h4, hlam]
                      · linarith only [h3495, h3570, hlam]
                · linarith only [h3565, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h0, h2186, h3249, h3560, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3562_1]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                rcases p3562_3 (m.d 0 2) (by simp) with h3575 | h3575
                · rcases p3562_3 (m.d 1 2) (by simp) with h3576 | h3576
                  · linarith only [h0, h3576, hlam]
                  · rcases p3562_3 (m.d 2 3) (by simp) with h3578 | h3578
                    · linarith only [h3, h3578, hlam]
                    · rcases p3562_3 (m.d 2 4) (by simp) with h3580 | h3580
                      · linarith only [h3580, h4, hlam]
                      · linarith only [h3560, h3580, hlam]
                · linarith only [h3575, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h0, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h9, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h2186, h3249, h3560, h9, hlam, p3562_1]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h2031, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h3, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h0, h3, h3558, h3561, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3562_1]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h3495, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h3558, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h4, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                rcases p3562_3 (m.d 0 2) (by simp) with h3595 | h3595
                · rcases p3562_3 (m.d 1 2) (by simp) with h3596 | h3596
                  · linarith only [h3596, hlam, p3562_0]
                  · rcases p3562_3 (m.d 2 3) (by simp) with h3598 | h3598
                    · linarith only [h3495, h3598, hlam]
                    · linarith only [h3598, h9, hlam]
                · linarith only [h0, h3595, hlam]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h0, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3562_1]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h0, h2031, h3, h3495, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3562_1]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h5, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                rcases p3562_3 (m.d 0 2) (by simp) with h3606 | h3606
                · rcases p3562_3 (m.d 1 2) (by simp) with h3607 | h3607
                  · linarith only [h3607, hlam, p3562_0]
                  · rcases p3562_3 (m.d 2 3) (by simp) with h3609 | h3609
                    · linarith only [h3558, h3609, hlam]
                    · linarith only [h3609, h9, hlam]
                · linarith only [h0, h3606, hlam]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h9, hc12, hc25, hlam, hphi, p3562_1]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [h3560, hlam, p3562_0]
              · have p3562_0 := h3562c.1
                have p3562_1 := h3562c.2.1
                have p3562_2 := h3562c.2.2.1
                have p3562_3 := h3562c.2.2.2
                linarith only [hlam, p3562_0]
            · linarith only [h3495, h3561, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3617 | h3617
            · linarith only [h0, h3, h3495, h3560, h3617, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h3495, h3617, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2031 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h2186 | h2186
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2031 h2186
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2031 h2186

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h2031 | h2031
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2031
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2031

set_option maxHeartbeats 7222000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9

set_option maxHeartbeats 9616000 in
set_option maxHeartbeats 9616000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s8 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8

end R2N4
