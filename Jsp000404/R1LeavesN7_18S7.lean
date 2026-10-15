import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S5
import Jsp000404.R1LeavesN7_18S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2947 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3245 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3470 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h4063 | h4063
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4064 | h4064
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4065 | h4065
      · linarith only [h0, h4, h4065, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4067 | h4067
        · linarith only [h0, h2947, h4067, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4069 | h4069
          · linarith only [h0, h3245, h4069, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4071 | h4071
            · linarith only [h1, h3470, h4071, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4073 | h4073
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4074 | h4074
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4075 | h4075
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4076 | h4076
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4077 | h4077
                      · rcases h0bigk with h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c | h4078c
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          rcases p4078_3 (m.d 0 1) (by simp) with h4080 | h4080
                          · rcases p4078_3 (m.d 0 2) (by simp) with h4081 | h4081
                            · linarith only [h0, h4081, hlam]
                            · rcases p4078_3 (m.d 0 3) (by simp) with h4083 | h4083
                              · linarith only [h1, h4083, hlam]
                              · linarith only [h4, h4083, hlam]
                          · linarith only [h0, h4080, hlam]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h4063, h4077, hc01, hc45, hlam, hphi, ht0b, ht5b, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h3470, h4063, h4077, hc01, hc45, hlam, hphi, ht0b, ht5b, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          rcases p4078_3 (m.d 0 1) (by simp) with h4089 | h4089
                          · rcases p4078_3 (m.d 0 2) (by simp) with h4090 | h4090
                            · linarith only [h0, h4090, hlam]
                            · rcases p4078_3 (m.d 0 3) (by simp) with h4092 | h4092
                              · linarith only [h1, h4092, hlam]
                              · linarith only [h4063, h4092, hlam]
                          · linarith only [h3, h4089, hlam]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h0, hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h4, hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h2947, hlam, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h3245, hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h1, hlam, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h0, h3470, h4074, hc12, hc23, hlam, hphi, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h3470, hlam, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h3470, h4074, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h2, hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h3470, h4074, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h0, h3245, h3470, h4074, hc12, hc23, hlam, hphi, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h3, hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h4063, hlam, p4078_0]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [h4064, hlam, p4078_1]
                        · have p4078_0 := h4078c.1
                          have p4078_1 := h4078c.2.1
                          have p4078_2 := h4078c.2.2.1
                          have p4078_3 := h4078c.2.2.2
                          linarith only [hlam, p4078_0]
                      · linarith only [h3470, h4064, h4077, hlam]
                    · linarith only [h0, h2947, h3470, h4063, h4064, h4076, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h3470, h4073, h4075, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4119 | h4119
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4120 | h4120
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4121 | h4121
                      · rcases h0bigk with h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c | h4122c
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          rcases p4122_3 (m.d 0 1) (by simp) with h4124 | h4124
                          · rcases p4122_3 (m.d 0 2) (by simp) with h4125 | h4125
                            · linarith only [h0, h4125, hlam]
                            · rcases p4122_3 (m.d 0 3) (by simp) with h4127 | h4127
                              · linarith only [h1, h4127, hlam]
                              · linarith only [h4, h4127, hlam]
                          · linarith only [h0, h4124, hlam]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h1, h4073, h4121, hc01, hc45, hlam, hphi, ht0b, ht5b, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h1, h3470, h4073, h4121, hc01, hc45, hlam, hphi, ht0b, ht5b, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          rcases p4122_3 (m.d 0 1) (by simp) with h4133 | h4133
                          · rcases p4122_3 (m.d 0 2) (by simp) with h4134 | h4134
                            · linarith only [h0, h4134, hlam]
                            · rcases p4122_3 (m.d 0 3) (by simp) with h4136 | h4136
                              · linarith only [h1, h4136, hlam]
                              · linarith only [h4063, h4136, hlam]
                          · linarith only [h3, h4133, hlam]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h0, hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h4, hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h2947, hlam, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h3245, hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h1, hlam, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h4, hc02, hc23, hlam, hphi, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h3470, hlam, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h0, h3245, h4, h4074, hc12, hc34, hlam, hphi, ht23, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h2, hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h3470, hc03, hc34, hlam, hphi, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h0, h3245, h3470, hc12, hc34, hlam, hphi, ht23, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h3, hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h4063, hlam, p4122_0]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [h4064, hlam, p4122_1]
                        · have p4122_0 := h4122c.1
                          have p4122_1 := h4122c.2.1
                          have p4122_2 := h4122c.2.2.1
                          have p4122_3 := h4122c.2.2.2
                          linarith only [hlam, p4122_0]
                      · linarith only [h0, h4, h4074, h4121, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h2947, h3470, h4063, h4064, h4120, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h4, h4073, h4119, hlam]
              · linarith only [h3470, h4063, h4073, hc13, hc34, hlam, hphi]
    · linarith only [h3470, h4063, h4064, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4165 | h4165
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4166 | h4166
      · linarith only [h0, h4, h4166, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4168 | h4168
        · linarith only [h0, h2947, h4168, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4170 | h4170
          · linarith only [h0, h3245, h4170, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4172 | h4172
            · linarith only [h1, h3470, h4172, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4174 | h4174
              · linarith only [h1, h4063, h4174, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4176 | h4176
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4177 | h4177
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4178 | h4178
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4179 | h4179
                      · rcases h0bigk with h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c | h4180c
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          rcases p4180_3 (m.d 0 1) (by simp) with h4182 | h4182
                          · rcases p4180_3 (m.d 0 2) (by simp) with h4183 | h4183
                            · linarith only [h0, h4183, hlam]
                            · rcases p4180_3 (m.d 0 3) (by simp) with h4185 | h4185
                              · linarith only [h1, h4185, hlam]
                              · linarith only [h4, h4185, hlam]
                          · linarith only [h0, h4182, hlam]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          rcases p4180_3 (m.d 0 1) (by simp) with h4189 | h4189
                          · rcases p4180_3 (m.d 0 2) (by simp) with h4190 | h4190
                            · linarith only [h0, h4190, hlam]
                            · rcases p4180_3 (m.d 0 3) (by simp) with h4192 | h4192
                              · linarith only [h1, h4192, hlam]
                              · rcases p4180_3 (m.d 0 4) (by simp) with h4194 | h4194
                                · linarith only [h2, h4194, hlam]
                                · linarith only [h3470, h4194, hlam]
                          · linarith only [h1, h4189, hlam]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h4165, hc01, hc45, hlam, hphi, ht0b, ht5b, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          rcases p4180_3 (m.d 0 1) (by simp) with h4199 | h4199
                          · rcases p4180_3 (m.d 0 2) (by simp) with h4200 | h4200
                            · linarith only [h0, h4200, hlam]
                            · rcases p4180_3 (m.d 0 3) (by simp) with h4202 | h4202
                              · linarith only [h1, h4202, hlam]
                              · rcases p4180_3 (m.d 0 4) (by simp) with h4204 | h4204
                                · linarith only [h2, h4204, hlam]
                                · linarith only [h4165, h4204, hlam]
                          · linarith only [h3, h4199, hlam]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h0, hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h4, hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h2947, hlam, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h3245, hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h1, hlam, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h0, h4063, h4176, h4179, hc12, hc23, hlam, hphi, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h3470, hlam, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h4063, hlam, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h2, hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h3470, h4176, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h0, h3470, h4, h4063, h4176, hc12, hc23, hlam, hphi, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h3, hlam, p4180_0]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h0, h4, h4063, h4176, h4179, hc12, hc23, hlam, hphi, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [h4165, hlam, p4180_1]
                        · have p4180_0 := h4180c.1
                          have p4180_1 := h4180c.2.1
                          have p4180_2 := h4180c.2.2.1
                          have p4180_3 := h4180c.2.2.2
                          linarith only [hlam, p4180_0]
                      · linarith only [h3470, h4165, h4179, hlam]
                    · linarith only [h0, h2947, h3470, h4165, h4178, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h3470, h4, h4176, h4177, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4231 | h4231
                  · linarith only [h0, h4, h4063, h4176, h4231, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4233 | h4233
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4234 | h4234
                      · rcases h0bigk with h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          rcases p4235_3 (m.d 0 1) (by simp) with h4237 | h4237
                          · rcases p4235_3 (m.d 0 2) (by simp) with h4238 | h4238
                            · linarith only [h0, h4238, hlam]
                            · rcases p4235_3 (m.d 0 3) (by simp) with h4240 | h4240
                              · linarith only [h1, h4240, hlam]
                              · linarith only [h4, h4240, hlam]
                          · linarith only [h0, h4237, hlam]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          rcases p4235_3 (m.d 0 1) (by simp) with h4244 | h4244
                          · rcases p4235_3 (m.d 0 2) (by simp) with h4245 | h4245
                            · linarith only [h0, h4245, hlam]
                            · rcases p4235_3 (m.d 0 3) (by simp) with h4247 | h4247
                              · linarith only [h1, h4247, hlam]
                              · rcases p4235_3 (m.d 0 4) (by simp) with h4249 | h4249
                                · linarith only [h2, h4249, hlam]
                                · linarith only [h3470, h4249, hlam]
                          · linarith only [h1, h4244, hlam]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h4165, hc01, hc45, hlam, hphi, ht0b, ht5b, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          rcases p4235_3 (m.d 0 1) (by simp) with h4254 | h4254
                          · rcases p4235_3 (m.d 0 2) (by simp) with h4255 | h4255
                            · linarith only [h0, h4255, hlam]
                            · rcases p4235_3 (m.d 0 3) (by simp) with h4257 | h4257
                              · linarith only [h1, h4257, hlam]
                              · rcases p4235_3 (m.d 0 4) (by simp) with h4259 | h4259
                                · linarith only [h2, h4259, hlam]
                                · linarith only [h4165, h4259, hlam]
                          · linarith only [h3, h4254, hlam]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h0, hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h4, hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h2947, hlam, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h3245, hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h1, hlam, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h0, h4, h4231, h4234, hc12, hc34, hlam, hphi, ht23, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h3470, hlam, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h4063, hlam, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h2, hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h0, h2947, h4176, hc12, hc34, hlam, hphi, ht23, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h2947, h4176, hc03, hc34, hlam, hphi, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h2947, h3, h4166, h4174, h4176, hc12, hc34, hlam, hphi, ht23, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h3, hlam, p4235_0]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h0, h3245, h4176, h4233, hc12, hc34, hlam, hphi, ht23, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h1, h3245, h4166, h4176, h4233, hc12, hc34, hlam, hphi, ht23, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [h4165, hlam, p4235_1]
                        · have p4235_0 := h4235c.1
                          have p4235_1 := h4235c.2.1
                          have p4235_2 := h4235c.2.2.1
                          have p4235_3 := h4235c.2.2.2
                          linarith only [hlam, p4235_0]
                      · linarith only [h2947, h4165, h4176, h4234, hlam]
                    · linarith only [h2947, h4165, h4233, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4285 | h4285
      · linarith only [h0, h4, h4285, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4287 | h4287
        · linarith only [h0, h2947, h4287, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4289 | h4289
          · linarith only [h0, h3245, h4289, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4291 | h4291
            · linarith only [h1, h3470, h4291, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4293 | h4293
              · linarith only [h1, h4063, h4293, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4295 | h4295
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4296 | h4296
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4297 | h4297
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4298 | h4298
                      · linarith only [h0, h3470, h4, h4165, h4295, h4298, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h3470, h4, h4295, h4297, h4298, hc12, hc23, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4301 | h4301
                      · linarith only [h0, h2947, h4297, h4301, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c | h4303c
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          rcases p4303_3 (m.d 0 1) (by simp) with h4305 | h4305
                          · rcases p4303_3 (m.d 0 2) (by simp) with h4306 | h4306
                            · linarith only [h0, h4306, hlam]
                            · rcases p4303_3 (m.d 0 3) (by simp) with h4308 | h4308
                              · linarith only [h1, h4308, hlam]
                              · linarith only [h4, h4308, hlam]
                          · linarith only [h0, h4305, hlam]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          rcases p4303_3 (m.d 0 1) (by simp) with h4312 | h4312
                          · rcases p4303_3 (m.d 0 2) (by simp) with h4313 | h4313
                            · linarith only [h0, h4313, hlam]
                            · rcases p4303_3 (m.d 0 3) (by simp) with h4315 | h4315
                              · linarith only [h1, h4315, hlam]
                              · rcases p4303_3 (m.d 0 4) (by simp) with h4317 | h4317
                                · linarith only [h2, h4317, hlam]
                                · linarith only [h3470, h4317, hlam]
                          · linarith only [h1, h4312, hlam]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          rcases p4303_3 (m.d 0 1) (by simp) with h4321 | h4321
                          · rcases p4303_3 (m.d 0 2) (by simp) with h4322 | h4322
                            · linarith only [h0, h4322, hlam]
                            · rcases p4303_3 (m.d 0 3) (by simp) with h4324 | h4324
                              · linarith only [h1, h4324, hlam]
                              · rcases p4303_3 (m.d 0 4) (by simp) with h4326 | h4326
                                · linarith only [h2, h4326, hlam]
                                · rcases p4303_3 (m.d 0 5) (by simp) with h4328 | h4328
                                  · linarith only [h3, h4328, hlam]
                                  · linarith only [h4165, h4328, hlam]
                          · linarith only [h2, h4321, hlam]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          rcases p4303_3 (m.d 0 1) (by simp) with h4332 | h4332
                          · rcases p4303_3 (m.d 0 2) (by simp) with h4333 | h4333
                            · linarith only [h0, h4333, hlam]
                            · rcases p4303_3 (m.d 0 3) (by simp) with h4335 | h4335
                              · linarith only [h1, h4335, hlam]
                              · rcases p4303_3 (m.d 0 4) (by simp) with h4337 | h4337
                                · linarith only [h2, h4337, hlam]
                                · rcases p4303_3 (m.d 0 5) (by simp) with h4339 | h4339
                                  · linarith only [h3, h4339, hlam]
                                  · rcases h2bigk with h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c | h4341c
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h3470, h4, h4165, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4303_1, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h2947, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h3245, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h0, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4285, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4287, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4289, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      rcases p4341_3 (m.d 0 2) (by simp) with h4352 | h4352
                                      · linarith only [h4352, hlam, p4341_0]
                                      · rcases p4341_3 (m.d 1 2) (by simp) with h4354 | h4354
                                        · linarith only [h4285, h4354, hlam]
                                        · rcases p4341_3 (m.d 2 3) (by simp) with h4356 | h4356
                                          · rcases p4341_3 (m.d 2 4) (by simp) with h4357 | h4357
                                            · linarith only [h4295, h4357, hlam]
                                            · linarith only [h2947, h4357, hlam]
                                          · linarith only [h4356, hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      rcases p4341_3 (m.d 0 2) (by simp) with h4361 | h4361
                                      · linarith only [h4, h4361, hlam]
                                      · linarith only [h0, h4361, hlam]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h3470, h4, h4295, hc02, hc23, hlam, hphi, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h0, h3245, hc12, hc23, hlam, hphi, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h0, h4297, hc12, hc45, hlam, hphi, ht23, ht34, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4297, hc12, hc45, hlam, hphi, ht23, ht34, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4295, hlam, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [hlam, p4341_0]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4297, hlam, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      rcases p4341_3 (m.d 0 2) (by simp) with h4372 | h4372
                                      · linarith only [h4372, hlam, p4341_0]
                                      · rcases p4341_3 (m.d 1 2) (by simp) with h4374 | h4374
                                        · linarith only [h4289, h4374, hlam]
                                        · rcases p4341_3 (m.d 2 3) (by simp) with h4376 | h4376
                                          · rcases p4341_3 (m.d 2 4) (by simp) with h4377 | h4377
                                            · linarith only [h4297, h4377, hlam]
                                            · linarith only [h2947, h4377, hlam]
                                          · linarith only [h4, h4376, hlam]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      rcases p4341_3 (m.d 0 2) (by simp) with h4381 | h4381
                                      · linarith only [h3245, h4381, hlam]
                                      · linarith only [h0, h4381, hlam]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h4296, hlam, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [h0, h2947, hc12, hc25, hlam, hphi, p4341_1]
                                    · have p4341_0 := h4341c.1
                                      have p4341_1 := h4341c.2.1
                                      have p4341_2 := h4341c.2.2.1
                                      have p4341_3 := h4341c.2.2.2
                                      linarith only [hlam, p4341_0]
                          · linarith only [h3, h4332, hlam]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h0, hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h4, hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h2947, hlam, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h3245, hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h1, hlam, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h0, h3470, hc12, hc34, hlam, hphi, ht23, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h3470, hlam, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h4063, hlam, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h2, hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h0, h2947, hc12, hc24, hlam, hphi, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h3470, h4301, hc03, hc35, hlam, hphi, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h4165, hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h3, hlam, p4303_0]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h0, h4, h4063, hc12, hc35, hlam, hphi, ht23, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [h4165, hc04, hc45, hlam, hphi, p4303_1]
                        · have p4303_0 := h4303c.1
                          have p4303_1 := h4303c.2.1
                          have p4303_2 := h4303c.2.2.1
                          have p4303_3 := h4303c.2.2.2
                          linarith only [hlam, p4303_0]
                  · linarith only [h0, h3470, h4, h4295, h4296, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4409 | h4409
                  · linarith only [h0, h4, h4063, h4295, h4409, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4411 | h4411
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4412 | h4412
                      · rcases h0bigk with h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c | h4413c
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          rcases p4413_3 (m.d 0 1) (by simp) with h4415 | h4415
                          · rcases p4413_3 (m.d 0 2) (by simp) with h4416 | h4416
                            · linarith only [h0, h4416, hlam]
                            · rcases p4413_3 (m.d 0 3) (by simp) with h4418 | h4418
                              · linarith only [h1, h4418, hlam]
                              · linarith only [h4, h4418, hlam]
                          · linarith only [h0, h4415, hlam]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          rcases p4413_3 (m.d 0 1) (by simp) with h4422 | h4422
                          · rcases p4413_3 (m.d 0 2) (by simp) with h4423 | h4423
                            · linarith only [h0, h4423, hlam]
                            · rcases p4413_3 (m.d 0 3) (by simp) with h4425 | h4425
                              · linarith only [h1, h4425, hlam]
                              · rcases p4413_3 (m.d 0 4) (by simp) with h4427 | h4427
                                · linarith only [h2, h4427, hlam]
                                · linarith only [h3470, h4427, hlam]
                          · linarith only [h1, h4422, hlam]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          rcases p4413_3 (m.d 0 1) (by simp) with h4431 | h4431
                          · rcases p4413_3 (m.d 0 2) (by simp) with h4432 | h4432
                            · linarith only [h0, h4432, hlam]
                            · rcases p4413_3 (m.d 0 3) (by simp) with h4434 | h4434
                              · linarith only [h1, h4434, hlam]
                              · rcases p4413_3 (m.d 0 4) (by simp) with h4436 | h4436
                                · linarith only [h2, h4436, hlam]
                                · rcases p4413_3 (m.d 0 5) (by simp) with h4438 | h4438
                                  · linarith only [h3, h4438, hlam]
                                  · linarith only [h4165, h4438, hlam]
                          · linarith only [h2, h4431, hlam]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          rcases p4413_3 (m.d 0 1) (by simp) with h4442 | h4442
                          · rcases p4413_3 (m.d 0 2) (by simp) with h4443 | h4443
                            · linarith only [h0, h4443, hlam]
                            · rcases p4413_3 (m.d 0 3) (by simp) with h4445 | h4445
                              · linarith only [h1, h4445, hlam]
                              · rcases p4413_3 (m.d 0 4) (by simp) with h4447 | h4447
                                · linarith only [h2, h4447, hlam]
                                · rcases p4413_3 (m.d 0 5) (by simp) with h4449 | h4449
                                  · linarith only [h3, h4449, hlam]
                                  · rcases h2bigk with h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c | h4451c
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4, h4409, h4412, hc12, hc34, hlam, hphi, ht23, p4451_1]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h2947, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h3245, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h0, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4285, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4287, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4289, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4409, h4412, hc02, hc34, hlam, hphi, ht23, p4451_1]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4409, h4412, hc12, hc34, hlam, hphi, ht23, p4451_1]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4295, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4409, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      rcases p4451_3 (m.d 0 2) (by simp) with h4467 | h4467
                                      · linarith only [h4467, hlam, p4451_0]
                                      · rcases p4451_3 (m.d 1 2) (by simp) with h4469 | h4469
                                        · linarith only [h4287, h4469, hlam]
                                        · rcases p4451_3 (m.d 2 3) (by simp) with h4471 | h4471
                                          · linarith only [h4295, h4471, hlam]
                                          · linarith only [h4, h4471, hlam]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      rcases p4451_3 (m.d 0 2) (by simp) with h4474 | h4474
                                      · linarith only [h2947, h4474, hlam]
                                      · linarith only [h0, h4474, hlam]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h0, h4, h4295, hc12, hc34, hlam, hphi, ht23, p4451_1]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h0, h3245, h4295, hc12, hc34, hlam, hphi, ht23, p4451_1]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      rcases p4451_3 (m.d 0 2) (by simp) with h4480 | h4480
                                      · linarith only [h4480, hlam, p4451_0]
                                      · rcases p4451_3 (m.d 1 2) (by simp) with h4482 | h4482
                                        · linarith only [h4289, h4482, hlam]
                                        · rcases p4451_3 (m.d 2 3) (by simp) with h4484 | h4484
                                          · linarith only [h4409, h4484, hlam]
                                          · linarith only [h4, h4484, hlam]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      rcases p4451_3 (m.d 0 2) (by simp) with h4487 | h4487
                                      · linarith only [h3245, h4487, hlam]
                                      · linarith only [h0, h4487, hlam]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p4451_1]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [h4411, hlam, p4451_0]
                                    · have p4451_0 := h4451c.1
                                      have p4451_1 := h4451c.2.1
                                      have p4451_2 := h4451c.2.2.1
                                      have p4451_3 := h4451c.2.2.2
                                      linarith only [hlam, p4451_0]
                          · linarith only [h3, h4442, hlam]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h0, hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h4, hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h2947, hlam, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h3245, hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h1, hlam, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h0, h4, hc12, hc23, hlam, hphi, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h3470, hlam, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h4063, hlam, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h2, hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h0, h2947, h4295, hc12, hc34, hlam, hphi, ht23, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h2947, h4295, hc03, hc34, hlam, hphi, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h4165, hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h3, hlam, p4413_0]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h0, h3245, hc12, hc25, hlam, hphi, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h1, h4063, h4285, h4412, hc12, hc34, hlam, hphi, ht23, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [h4165, h4295, h4411, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4413_1]
                        · have p4413_0 := h4413c.1
                          have p4413_1 := h4413c.2.1
                          have p4413_2 := h4413c.2.2.1
                          have p4413_3 := h4413c.2.2.2
                          linarith only [hlam, p4413_0]
                      · linarith only [h4295, h4411, h4412, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4515 | h4515
                      · linarith only [h0, h4, h4295, h4411, h4515, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h4, h4295, h4515, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2947 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3245 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h3470 | h3470
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2947 h3245 h3470
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2947 h3245 h3470

set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h2947 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h3245 | h3245
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2947 h3245
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2947 h3245

set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h2947 | h2947
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2947
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h2947

set_option maxHeartbeats 9028000 in
set_option maxHeartbeats 9028000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 9342000 in
set_option maxHeartbeats 9342000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s3 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4518 | h4518
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4519 | h4519
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4520 | h4520
        · linarith only [h0, h3, h4520, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4522 | h4522
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4523 | h4523
            · linarith only [h1, h3, h4523, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4525 | h4525
              · linarith only [h2, h3, h4525, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4527 | h4527
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4528 | h4528
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4529 | h4529
                    · linarith only [h0, h4520, h4529, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4531 | h4531
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4532 | h4532
                        · linarith only [h1, h3, h4523, h4529, h4532, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h4527, h4532, hc23, hc35, hlam, hphi]
                      · linarith only [h4522, h4523, h4531, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h3, h4519, h4527, h4528, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h4518, h4520, h4527, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4538 | h4538
            · linarith only [h1, h3, h4538, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4540 | h4540
              · linarith only [h0, h3, h4519, h4540, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4542 | h4542
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4543 | h4543
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4544 | h4544
                    · linarith only [h0, h4520, h4544, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4546 | h4546
                      · linarith only [h1, h4522, h4546, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4548 | h4548
                        · linarith only [h1, h3, h4538, h4544, h4548, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h3, h4542, h4548, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h3, h4519, h4542, h4543, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h4518, h4520, h4542, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4553 | h4553
        · linarith only [h2, h3, h4519, h4553, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4555 | h4555
          · linarith only [h4518, h4519, h4555, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4557 | h4557
            · linarith only [h2, h3, h4518, h4519, h4557, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4559 | h4559
              · linarith only [h2, h3, h4559, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4561 | h4561
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4562 | h4562
                  · linarith only [h0, h4519, h4562, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4564 | h4564
                    · linarith only [h0, h4553, h4564, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4566 | h4566
                      · linarith only [h1, h3, h4555, h4564, h4566, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4568 | h4568
                        · linarith only [h1, h4557, h4568, hlam]
                        · linarith only [h0, h3, h4561, h4568, hc23, hc35, hlam, hphi]
                · linarith only [h4518, h4519, h4561, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4572 | h4572
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4573 | h4573
        · linarith only [h1, h3, h4518, h4573, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4575 | h4575
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4576 | h4576
            · linarith only [h1, h3, h4576, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4578 | h4578
              · linarith only [h1, h3, h4518, h4572, h4578, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4580 | h4580
                · linarith only [h0, h3, h4518, h4580, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4582 | h4582
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4583 | h4583
                    · linarith only [h0, h3, h4573, h4583, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4585 | h4585
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4586 | h4586
                        · linarith only [h1, h3, h4576, h4583, h4586, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4588 | h4588
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4589 | h4589
                            · linarith only [h1, h3, h4580, h4586, h4589, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4591 | h4591
                              · linarith only [h1, h3, h4578, h4580, h4582, h4591, hc05, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1, h3, h4580, h4582, h4583, h4588, h4591, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h4518, h4575, h4582, h4588, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h1, h3, h4575, h4580, h4582, h4585, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h4518, h4572, h4576, h4582, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h4518, h4572, h4575, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4598 | h4598
        · linarith only [h0, h3, h4598, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4600 | h4600
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4601 | h4601
            · linarith only [h1, h3, h4601, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4603 | h4603
              · linarith only [h1, h3, h4600, h4603, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4605 | h4605
                · linarith only [h0, h4518, h4605, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4607 | h4607
                  · linarith only [h0, h4572, h4607, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4609 | h4609
                    · linarith only [h0, h4598, h4609, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4611 | h4611
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4612 | h4612
                        · linarith only [h1, h4601, h4612, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4614 | h4614
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4615 | h4615
                            · linarith only [h1, h3, h4611, h4612, h4615, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4617 | h4617
                              · linarith only [h1, h3, h4603, h4611, h4614, h4615, h4617, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h1, h3, h4609, h4611, h4617, hc34, hc45, hlam, hphi]
                          · linarith only [h1, h3, h4611, h4614, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h4600, h4601, h4611, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4622 | h4622
            · linarith only [h2, h3, h4600, h4622, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4624 | h4624
              · linarith only [h2, h3, h4624, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4626 | h4626
                · linarith only [h0, h3, h4518, h4626, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4628 | h4628
                  · linarith only [h1, h4572, h4600, h4626, h4628, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4630 | h4630
                    · linarith only [h0, h4598, h4630, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4632 | h4632
                      · linarith only [h1, h4600, h4632, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4634 | h4634
                        · linarith only [h2, h3, h4622, h4630, h4632, h4634, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h4636 | h4636
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4637 | h4637
                            · linarith only [h0, h3, h4634, h4637, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h4518, h4600, h4636, h4637, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h4640 | h4640
                            · linarith only [h0, h4518, h4622, h4636, h4640, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h4642 | h4642
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4643 | h4643
                                · rcases h0bigk with h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c | h4644c
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h0, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h0, h3, h4518, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h2, h3, h4626, h4632, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h3, hlam, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h0, hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4518, hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4572, hlam, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4598, hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h1, hlam, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h0, h1, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4600, hlam, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4622, hlam, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h2, hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h0, h2, h3, h4624, h4636, h4642, hc12, hc34, hlam, hphi, ht23, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h2, h3, h4624, h4636, h4642, hc03, hc34, hlam, hphi, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4624, hlam, p4644_0]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4624, h4636, h4642, hc01, hc34, hlam, hphi, ht12, ht23, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h0, h4624, h4636, h4642, hc12, hc34, hlam, hphi, ht23, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h1, h4624, h4626, h4636, h4642, hc12, hc34, hlam, hphi, ht23, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [h4624, h4636, h4642, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p4644_1]
                                  · have p4644_0 := h4644c.1
                                    have p4644_1 := h4644c.2.1
                                    have p4644_2 := h4644c.2.2.1
                                    have p4644_3 := h4644c.2.2.2
                                    linarith only [hlam, p4644_0]
                                · linarith only [h4636, h4642, h4643, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h4671 | h4671
                                · linarith only [h0, h4518, h4636, h4642, h4671, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h4518, h4636, h4671, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
