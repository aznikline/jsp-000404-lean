import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S12
import Jsp000404.R1LeavesN7_30S13
import Jsp000404.R1LeavesN7_30S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2808 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3661 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 2 5 (by decide) (by decide) with h4100 | h4100
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4101 | h4101
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4102 | h4102
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4103 | h4103
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4104 | h4104
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4105 | h4105
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4106 | h4106
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4107 | h4107
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4108 | h4108
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4109 | h4109
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4110 | h4110
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4111 | h4111
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4112 | h4112
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4113 | h4113
                            · linarith only [h4101, h4113, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h4103, h4113, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h3661, h4100, h4101, h4103, h4111, h4112, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h3661, h4102, h4110, h4111, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h4101, h4110, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h3661, h4100, h4101, h4103, h4105, h4109, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h3661, h4100, h4102, h4105, h4107, h4108, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                · linarith only [h4101, h4107, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h2808, h4100, h4104, h4106, hlam]
            · linarith only [h2808, h4100, h4104, h4105, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4124 | h4124
            · linarith only [h3661, h4100, h4104, h4124, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4126 | h4126
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4127 | h4127
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4128 | h4128
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4129 | h4129
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4130 | h4130
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4131 | h4131
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4132 | h4132
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4133 | h4133
                            · linarith only [h4101, h4133, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h4101, h4103, h4133, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h4101, h4103, h4124, h4132, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h2494, h4124, h4126, h4130, h4131, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h4101, h4130, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1991, h4103, h4129, hlam]
                  · linarith only [h1106, h4102, h4128, hlam]
                · linarith only [h1106, h4101, h4127, hlam]
              · linarith only [h4100, h4126, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h3661, h4100, h4103, hlam]
      · linarith only [h3661, h4100, h4101, h4102, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4145 | h4145
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4146 | h4146
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4147 | h4147
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4148 | h4148
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4149 | h4149
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4150 | h4150
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4151 | h4151
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4152 | h4152
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4153 | h4153
                      · linarith only [h2808, h4100, h4101, h4147, h4153, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2808, h4100, h4147, h4150, h4153, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h4146, h4152, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h4145, h4151, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4158 | h4158
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4159 | h4159
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4160 | h4160
                      · linarith only [h4147, h4150, h4160, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4162 | h4162
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4163 | h4163
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4164 | h4164
                            · rcases h2bigk with h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h0, hlam, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h2808, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h3661, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h2808, h4147, h4150, h4162, h4164, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                rcases p4165_3 (m.d 0 2) (by simp) with h4171 | h4171
                                · linarith only [h0, h4171, hlam]
                                · rcases p4165_3 (m.d 1 2) (by simp) with h4173 | h4173
                                  · rcases p4165_3 (m.d 2 3) (by simp) with h4174 | h4174
                                    · linarith only [h4147, h4174, hlam]
                                    · linarith only [h2808, h4174, hlam]
                                  · linarith only [h0, h4173, hlam]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h2494, h2808, h4100, hc01, hc12, hlam, hphi, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h2808, h4100, h4160, h4162, h4164, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h2808, h4100, h4147, hlam, p4165_2]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4100, h4147, h4162, h4164, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4147, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4160, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                rcases p4165_3 (m.d 0 2) (by simp) with h4186 | h4186
                                · linarith only [h2808, h4186, hlam]
                                · linarith only [h4100, h4186, hlam]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4100, h4148, h4162, h4164, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4148, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h2808, h4100, h4148, h4162, h4164, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                rcases p4165_3 (m.d 0 2) (by simp) with h4193 | h4193
                                · linarith only [h3661, h4193, hlam]
                                · linarith only [h4100, h4193, hlam]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4100, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4149, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4162, hlam, p4165_1]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [h4163, hlam, p4165_0]
                              · have p4165_0 := h4165c.1
                                have p4165_1 := h4165c.2.1
                                have p4165_2 := h4165c.2.2.1
                                have p4165_3 := h4165c.2.2.2
                                linarith only [hlam, p4165_0]
                            · linarith only [h1106, h4150, h4164, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h4146, h4163, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h2808, h4101, h4145, h4162, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2808, h4100, h4146, h4147, h4150, h4159, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h2808, h4100, h4101, h4145, h4147, h4158, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
              · linarith only [h4100, h4149, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h2808, h4147, h4148, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4208 | h4208
            · linarith only [h3661, h4100, h4147, h4208, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4210 | h4210
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4211 | h4211
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4212 | h4212
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4213 | h4213
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4214 | h4214
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4215 | h4215
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4216 | h4216
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4217 | h4217
                            · rcases h2bigk with h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c | h4218c
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h0, hlam, p4218_1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h2808, hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h3661, hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4215, h4217, hc45, hlam, hphi, ht0b, ht5b, p4218_1, u0elo1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4208, h4214, hc02, hc23, hlam, hphi, p4218_1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4147, hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4208, hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                rcases p4218_3 (m.d 0 2) (by simp) with h4228 | h4228
                                · linarith only [h0, h4228, hlam]
                                · linarith only [h4100, h4228, hlam]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                rcases p4218_3 (m.d 0 2) (by simp) with h4231 | h4231
                                · linarith only [h4231, hlam, p4218_0]
                                · rcases p4218_3 (m.d 1 2) (by simp) with h4233 | h4233
                                  · linarith only [h4147, h4233, hlam]
                                  · linarith only [h0, h4233, hlam]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4218_1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h3661, h4100, h4215, h4217, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4218_1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h2808, h4100, h4101, h4147, h4211, hlam, p4218_2]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                rcases p4218_3 (m.d 0 2) (by simp) with h4240 | h4240
                                · linarith only [h4240, hlam, p4218_0]
                                · rcases p4218_3 (m.d 1 2) (by simp) with h4242 | h4242
                                  · linarith only [h4208, h4242, hlam]
                                  · linarith only [h0, h4242, hlam]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h2494, h4210, hc01, hc24, hlam, hphi, ht12, p4218_1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4214, hlam, p4218_1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                rcases p4218_3 (m.d 0 2) (by simp) with h4248 | h4248
                                · linarith only [h3661, h4248, hlam]
                                · linarith only [h4100, h4248, hlam]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4100, hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4210, hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4215, hlam, p4218_1]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [h4216, hlam, p4218_0]
                              · have p4218_0 := h4218c.1
                                have p4218_1 := h4218c.2.1
                                have p4218_2 := h4218c.2.2.1
                                have p4218_3 := h4218c.2.2.2
                                linarith only [hlam, p4218_0]
                            · linarith only [h2808, h4101, h4146, h4217, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h4146, h4208, h4216, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h2808, h4100, h4101, h4147, h4211, h4215, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h4147, h4211, h4214, hlam]
                    · linarith only [h4146, h4213, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h4101, h4145, h4211, h4212, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4262 | h4262
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4263 | h4263
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4264 | h4264
                      · linarith only [h1106, h4211, h4264, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h2494, h4147, h4210, h4264, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4146, h4263, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h2494, h4145, h4147, h4210, h4262, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h4100, h4210, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h2808, h4100, h4101, h4146, hlam]
      · linarith only [h2808, h4100, h4145, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4272 | h4272
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4273 | h4273
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4274 | h4274
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4275 | h4275
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4276 | h4276
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4277 | h4277
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4278 | h4278
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4279 | h4279
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4280 | h4280
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4281 | h4281
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4282 | h4282
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4283 | h4283
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4284 | h4284
                            · linarith only [h4272, h4284, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h4272, h4274, h4284, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · linarith only [h4272, h4274, h4283, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h3661, h4273, h4281, h4282, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2808, h4272, h4281, hlam]
                    · linarith only [h3661, h4274, h4276, h4280, hlam]
                  · linarith only [h2808, h4273, h4275, h4279, hlam]
                · linarith only [h2808, h4272, h4275, h4278, hlam]
              · linarith only [h0, h2808, h4275, h4277, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2808, h4275, h4276, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4295 | h4295
            · linarith only [h0, h3661, h4275, h4295, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4297 | h4297
              · linarith only [h0, h4100, h4275, h4297, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4299 | h4299
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4300 | h4300
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4301 | h4301
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4302 | h4302
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4303 | h4303
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4304 | h4304
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4305 | h4305
                            · linarith only [h4272, h4305, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                            · linarith only [h4274, h4305, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h4272, h4274, h4304, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h0, h4273, h4295, h4302, h4303, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h4272, h4302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1991, h4274, h4301, hlam]
                  · linarith only [h1106, h4273, h4300, hlam]
                · linarith only [h1106, h4272, h4299, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4314 | h4314
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4315 | h4315
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4316 | h4316
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4317 | h4317
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4318 | h4318
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4319 | h4319
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4320 | h4320
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4321 | h4321
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4322 | h4322
                          · linarith only [h1991, h4274, h4315, h4322, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h3661, h4314, h4317, h4319, h4322, hc01, hc12, hlam, hphi]
                        · linarith only [h4273, h4321, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h2808, h4272, h4320, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4327 | h4327
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4328 | h4328
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4329 | h4329
                          · linarith only [h1991, h4319, h4329, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4331 | h4331
                            · linarith only [h4272, h4319, h4331, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases h2bigk with h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, hlam, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h2808, hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h3661, hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h4100, hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                rcases p4333_3 (m.d 0 2) (by simp) with h4339 | h4339
                                · linarith only [h0, h4339, hlam]
                                · rcases p4333_3 (m.d 1 2) (by simp) with h4341 | h4341
                                  · rcases p4333_3 (m.d 2 3) (by simp) with h4342 | h4342
                                    · linarith only [h4314, h4342, hlam]
                                    · linarith only [h2808, h4342, hlam]
                                  · linarith only [h0, h4341, hlam]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h2808, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h3661, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h3661, h4329, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h4314, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h4314, hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h3661, h4314, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h2494, h4100, h4314, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h4315, h4319, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h4315, hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h4327, hlam, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h4329, hlam, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h4316, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h4316, hlam, p4333_0]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h4328, hlam, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [h0, h3661, h4314, h4328, hc01, hc12, hlam, hphi, p4333_1]
                              · have p4333_0 := h4333c.1
                                have p4333_1 := h4333c.2.1
                                have p4333_2 := h4333c.2.2.1
                                have p4333_3 := h4333c.2.2.2
                                linarith only [hlam, p4333_0]
                        · linarith only [h0, h2808, h4273, h4328, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h2808, h4272, h4273, h4327, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h4273, h4318, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h2808, h4272, h4314, h4317, hlam]
              · linarith only [h0, h2808, h4314, h4316, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2808, h4314, h4315, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4371 | h4371
            · linarith only [h0, h3661, h4314, h4371, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4373 | h4373
              · linarith only [h0, h4100, h4314, h4373, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4375 | h4375
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4376 | h4376
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4377 | h4377
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4378 | h4378
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4379 | h4379
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4380 | h4380
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4381 | h4381
                            · linarith only [h0, h3661, h4272, h4274, h4381, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c | h4383c
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, hlam, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h2808, hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h3661, hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h4100, hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, h4373, h4378, h4380, hc01, hc23, hlam, hphi, ht12, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h4314, hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h4371, hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h4373, hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                rcases p4383_3 (m.d 0 2) (by simp) with h4394 | h4394
                                · linarith only [h4394, hlam, p4383_0]
                                · rcases p4383_3 (m.d 1 2) (by simp) with h4396 | h4396
                                  · linarith only [h4314, h4396, hlam]
                                  · linarith only [h0, h4396, hlam]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, h3661, hc01, hc23, hlam, hphi, ht12, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, h4373, hc01, hc23, hlam, hphi, ht12, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                rcases p4383_3 (m.d 0 2) (by simp) with h4403 | h4403
                                · linarith only [h4403, hlam, p4383_0]
                                · rcases p4383_3 (m.d 1 2) (by simp) with h4405 | h4405
                                  · linarith only [h4371, h4405, hlam]
                                  · linarith only [h0, h4405, hlam]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h4378, hlam, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, h4373, h4378, hc01, hc23, hlam, hphi, ht12, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                rcases p4383_3 (m.d 0 2) (by simp) with h4412 | h4412
                                · linarith only [h4412, hlam, p4383_0]
                                · rcases p4383_3 (m.d 1 2) (by simp) with h4414 | h4414
                                  · linarith only [h4373, h4414, hlam]
                                  · linarith only [h0, h4414, hlam]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h4379, hlam, p4383_1]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [h4380, hlam, p4383_0]
                              · have p4383_0 := h4383c.1
                                have p4383_1 := h4383c.2.1
                                have p4383_2 := h4383c.2.2.1
                                have p4383_3 := h4383c.2.2.2
                                linarith only [hlam, p4383_0]
                          · linarith only [h0, h3661, h4375, h4377, h4380, hc01, hc13, hlam, hphi]
                        · linarith only [h4273, h4314, h4379, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h4272, h4274, h4314, h4375, h4377, h4378, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4424 | h4424
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4425 | h4425
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4426 | h4426
                          · linarith only [h1991, h4377, h4426, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h4371, h4426, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h1106, h4273, h4314, h4425, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h1106, h4272, h4314, h4424, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1106, h4273, h4376, hlam]
                · linarith only [h1106, h4272, h4375, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4433 | h4433
        · linarith only [h4272, h4273, h4433, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4435 | h4435
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4436 | h4436
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4437 | h4437
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4438 | h4438
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4439 | h4439
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4440 | h4440
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4441 | h4441
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4442 | h4442
                        · linarith only [h4272, h4273, h4435, h4442, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h2808, h4435, h4439, h4442, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2808, h4272, h4441, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4446 | h4446
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4447 | h4447
                        · linarith only [h4272, h4273, h4435, h4447, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h2808, h4435, h4439, h4447, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2808, h4272, h4446, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4451 | h4451
                    · linarith only [h0, h3661, h4433, h4438, h4439, h4451, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4453 | h4453
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4454 | h4454
                        · linarith only [h1106, h4439, h4454, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4456 | h4456
                          · linarith only [h0, h3661, h4433, h4436, h4438, h4439, h4456, hc01, hc35, hlam, hphi, ht12, ht23]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4458 | h4458
                            · linarith only [h4272, h4451, h4458, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c | h4460c
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, hlam, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h2808, hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h3661, hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h4100, hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                rcases p4460_3 (m.d 0 2) (by simp) with h4466 | h4466
                                · linarith only [h0, h4466, hlam]
                                · rcases p4460_3 (m.d 1 2) (by simp) with h4468 | h4468
                                  · rcases p4460_3 (m.d 2 3) (by simp) with h4469 | h4469
                                    · linarith only [h4435, h4469, hlam]
                                    · linarith only [h2808, h4469, hlam]
                                  · linarith only [h0, h4468, hlam]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h2808, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h3661, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h2808, h4454, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h4435, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h4435, hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h3661, h4435, h4439, h4458, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h4454, hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h4436, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h4436, hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h4453, hlam, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h4456, hlam, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h4437, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h4437, hlam, p4460_0]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h2808, h4437, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [h0, h3661, h4437, hc01, hc12, hlam, hphi, p4460_1]
                              · have p4460_0 := h4460c.1
                                have p4460_1 := h4460c.2.1
                                have p4460_2 := h4460c.2.2.1
                                have p4460_3 := h4460c.2.2.2
                                linarith only [hlam, p4460_0]
                      · linarith only [h2808, h4272, h4453, hlam]
                · linarith only [h4272, h4273, h4438, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
              · linarith only [h0, h2808, h4435, h4437, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2808, h4435, h4436, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4496 | h4496
            · linarith only [h0, h3661, h4435, h4496, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4498 | h4498
              · linarith only [h0, h4100, h4435, h4498, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4500 | h4500
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4501 | h4501
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4502 | h4502
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4503 | h4503
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4504 | h4504
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4505 | h4505
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4506 | h4506
                            · linarith only [h0, h3661, h4272, h4433, h4506, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h2bigk with h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c | h4508c
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, hlam, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h2808, hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h3661, hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h4100, hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, h4498, h4503, h4505, hc01, hc23, hlam, hphi, ht12, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h4435, hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h4496, hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h4498, hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                rcases p4508_3 (m.d 0 2) (by simp) with h4519 | h4519
                                · linarith only [h4519, hlam, p4508_0]
                                · rcases p4508_3 (m.d 1 2) (by simp) with h4521 | h4521
                                  · linarith only [h4435, h4521, hlam]
                                  · linarith only [h0, h4521, hlam]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, h3661, hc01, hc23, hlam, hphi, ht12, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, h4498, hc01, hc23, hlam, hphi, ht12, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                rcases p4508_3 (m.d 0 2) (by simp) with h4528 | h4528
                                · linarith only [h4528, hlam, p4508_0]
                                · rcases p4508_3 (m.d 1 2) (by simp) with h4530 | h4530
                                  · linarith only [h4496, h4530, hlam]
                                  · linarith only [h0, h4530, hlam]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h4503, hlam, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, h4498, h4503, hc01, hc23, hlam, hphi, ht12, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                rcases p4508_3 (m.d 0 2) (by simp) with h4537 | h4537
                                · linarith only [h4537, hlam, p4508_0]
                                · rcases p4508_3 (m.d 1 2) (by simp) with h4539 | h4539
                                  · linarith only [h4498, h4539, hlam]
                                  · linarith only [h0, h4539, hlam]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h4504, hlam, p4508_1]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [h4505, hlam, p4508_0]
                              · have p4508_0 := h4508c.1
                                have p4508_1 := h4508c.2.1
                                have p4508_2 := h4508c.2.2.1
                                have p4508_3 := h4508c.2.2.2
                                linarith only [hlam, p4508_0]
                          · linarith only [h4496, h4502, h4505, hlam]
                        · linarith only [h1991, h4433, h4496, h4502, h4503, h4504, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h3661, h4272, h4433, h4435, h4500, h4502, h4503, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4549 | h4549
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4550 | h4550
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4551 | h4551
                          · linarith only [h0, h4496, h4502, h4551, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h4496, h4551, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h4435, h4501, h4550, hlam]
                      · linarith only [h4272, h4273, h4435, h4501, h4549, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4556 | h4556
                    · linarith only [h0, h3661, h4433, h4500, h4501, h4556, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4558 | h4558
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4559 | h4559
                        · linarith only [h1106, h4501, h4559, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h4435, h4559, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4272, h4435, h4558, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h1106, h4272, h4500, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4564 | h4564
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4565 | h4565
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4566 | h4566
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4567 | h4567
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4568 | h4568
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4569 | h4569
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4570 | h4570
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4571 | h4571
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4572 | h4572
                      · linarith only [h4272, h4564, h4566, h4572, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h2808, h4566, h4569, h4572, hc01, hc12, hlam, hphi]
                    · linarith only [h4565, h4571, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h4564, h4570, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4577 | h4577
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4578 | h4578
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4579 | h4579
                      · linarith only [h1106, h4569, h4579, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4581 | h4581
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4582 | h4582
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4583 | h4583
                            · rcases h2bigk with h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c | h4584c
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, hlam, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h2808, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h3661, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h4100, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                rcases p4584_3 (m.d 0 2) (by simp) with h4590 | h4590
                                · linarith only [h0, h4590, hlam]
                                · rcases p4584_3 (m.d 1 2) (by simp) with h4592 | h4592
                                  · rcases p4584_3 (m.d 2 3) (by simp) with h4593 | h4593
                                    · linarith only [h4566, h4593, hlam]
                                    · linarith only [h2808, h4593, hlam]
                                  · linarith only [h0, h4592, hlam]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h2808, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h3661, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h4100, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h4566, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h4566, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h4579, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h4100, h4566, hc01, hc13, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h4567, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h4567, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h2808, h4567, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h4100, h4567, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h0, h4568, hc01, hc12, hlam, hphi, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h4568, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h4581, hlam, p4584_1]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [h4582, hlam, p4584_0]
                              · have p4584_0 := h4584c.1
                                have p4584_1 := h4584c.2.1
                                have p4584_2 := h4584c.2.2.1
                                have p4584_3 := h4584c.2.2.2
                                linarith only [hlam, p4584_0]
                            · linarith only [h1106, h4569, h4583, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h3661, h4565, h4582, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                        · linarith only [h2808, h4564, h4581, hlam]
                    · linarith only [h3661, h4565, h4567, h4578, hlam]
                  · linarith only [h2808, h4564, h4566, h4577, hlam]
              · linarith only [h0, h2808, h4566, h4568, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2808, h4566, h4567, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4623 | h4623
            · linarith only [h0, h3661, h4566, h4623, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4625 | h4625
              · linarith only [h0, h4100, h4566, h4625, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4627 | h4627
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4628 | h4628
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4629 | h4629
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4630 | h4630
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4631 | h4631
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4632 | h4632
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4633 | h4633
                            · rcases h2bigk with h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c | h4634c
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, hlam, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h2808, hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h3661, hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h4100, hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, h4625, h4630, h4632, hc01, hc23, hlam, hphi, ht12, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h4566, hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h4623, hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h4625, hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                rcases p4634_3 (m.d 0 2) (by simp) with h4645 | h4645
                                · linarith only [h4645, hlam, p4634_0]
                                · rcases p4634_3 (m.d 1 2) (by simp) with h4647 | h4647
                                  · linarith only [h4566, h4647, hlam]
                                  · linarith only [h0, h4647, hlam]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, h3661, hc01, hc23, hlam, hphi, ht12, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, h4625, hc01, hc23, hlam, hphi, ht12, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                rcases p4634_3 (m.d 0 2) (by simp) with h4654 | h4654
                                · linarith only [h4654, hlam, p4634_0]
                                · rcases p4634_3 (m.d 1 2) (by simp) with h4656 | h4656
                                  · linarith only [h4623, h4656, hlam]
                                  · linarith only [h0, h4656, hlam]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h4630, hlam, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, h4625, h4630, hc01, hc23, hlam, hphi, ht12, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                rcases p4634_3 (m.d 0 2) (by simp) with h4663 | h4663
                                · linarith only [h4663, hlam, p4634_0]
                                · rcases p4634_3 (m.d 1 2) (by simp) with h4665 | h4665
                                  · linarith only [h4625, h4665, hlam]
                                  · linarith only [h0, h4665, hlam]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h4631, hlam, p4634_1]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [h4632, hlam, p4634_0]
                              · have p4634_0 := h4634c.1
                                have p4634_1 := h4634c.2.1
                                have p4634_2 := h4634c.2.2.1
                                have p4634_3 := h4634c.2.2.2
                                linarith only [hlam, p4634_0]
                            · linarith only [h4272, h4565, h4633, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h4565, h4632, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h4564, h4566, h4631, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h4566, h4627, h4630, hlam]
                    · linarith only [h4565, h4629, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h4272, h4564, h4627, h4628, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4678 | h4678
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4679 | h4679
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4680 | h4680
                      · linarith only [h1106, h4627, h4680, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h4566, h4680, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4565, h4679, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h4564, h4678, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
        · linarith only [h4272, h4564, h4565, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4686 | h4686
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4687 | h4687
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4688 | h4688
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4689 | h4689
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4690 | h4690
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4691 | h4691
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4692 | h4692
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4693 | h4693
                      · linarith only [h0, h2808, h4272, h4687, h4693, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2808, h4690, h4693, hc01, hc13, hlam, hphi]
                    · linarith only [h4686, h4692, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2808, h4272, h4690, h4691, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4698 | h4698
                  · linarith only [h0, h2808, h4564, h4690, h4698, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4700 | h4700
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4701 | h4701
                      · linarith only [h1106, h4690, h4701, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4703 | h4703
                        · linarith only [h4687, h4698, h4703, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4705 | h4705
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4706 | h4706
                            · rcases h2bigk with h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c | h4707c
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, hlam, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h2808, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h3661, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h4100, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                rcases p4707_3 (m.d 0 2) (by simp) with h4713 | h4713
                                · linarith only [h0, h4713, hlam]
                                · rcases p4707_3 (m.d 1 2) (by simp) with h4715 | h4715
                                  · rcases p4707_3 (m.d 2 3) (by simp) with h4716 | h4716
                                    · linarith only [h4687, h4716, hlam]
                                    · linarith only [h2808, h4716, hlam]
                                  · linarith only [h0, h4715, hlam]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h2808, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h2808, h4703, h4705, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h2808, h4703, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h4687, h4698, h4706, hc01, hc34, hlam, hphi, ht12, ht23, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h4687, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h4701, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h4703, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h4688, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h4688, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h2808, h4688, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h2808, h4688, h4703, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h4689, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h4689, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h0, h2808, h4689, hc01, hc12, hlam, hphi, p4707_1]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [h4705, hlam, p4707_0]
                              · have p4707_0 := h4707c.1
                                have p4707_1 := h4707c.2.1
                                have p4707_2 := h4707c.2.2.1
                                have p4707_3 := h4707c.2.2.2
                                linarith only [hlam, p4707_0]
                            · linarith only [h4686, h4706, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h0, h3661, h4686, h4705, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h4686, h4700, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h0, h2808, h4687, h4689, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2808, h4687, h4688, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4744 | h4744
            · linarith only [h0, h3661, h4687, h4744, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4746 | h4746
              · linarith only [h0, h4100, h4744, h4746, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4748 | h4748
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4749 | h4749
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4750 | h4750
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4751 | h4751
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4752 | h4752
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4753 | h4753
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4754 | h4754
                            · rcases h2bigk with h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c | h4755c
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h0, hlam, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h2808, hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h3661, hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h4100, hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h0, h4746, h4751, h4753, hc01, hc23, hlam, hphi, ht12, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h4687, hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h4744, hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h4746, hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                rcases p4755_3 (m.d 0 2) (by simp) with h4766 | h4766
                                · linarith only [h4766, hlam, p4755_0]
                                · rcases p4755_3 (m.d 1 2) (by simp) with h4768 | h4768
                                  · linarith only [h4687, h4768, hlam]
                                  · linarith only [h0, h4768, hlam]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h0, h3661, hc01, hc23, hlam, hphi, ht12, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h0, h4746, hc01, hc23, hlam, hphi, ht12, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                rcases p4755_3 (m.d 0 2) (by simp) with h4775 | h4775
                                · linarith only [h4775, hlam, p4755_0]
                                · rcases p4755_3 (m.d 1 2) (by simp) with h4777 | h4777
                                  · linarith only [h4744, h4777, hlam]
                                  · linarith only [h0, h4777, hlam]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h4751, hlam, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h2494, h4746, h4751, hc01, hc23, hlam, hphi, ht12, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                rcases p4755_3 (m.d 0 2) (by simp) with h4784 | h4784
                                · linarith only [h4784, hlam, p4755_0]
                                · rcases p4755_3 (m.d 1 2) (by simp) with h4786 | h4786
                                  · linarith only [h4746, h4786, hlam]
                                  · linarith only [h0, h4786, hlam]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h4752, hlam, p4755_1]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [h4753, hlam, p4755_0]
                              · have p4755_0 := h4755c.1
                                have p4755_1 := h4755c.2.1
                                have p4755_2 := h4755c.2.2.1
                                have p4755_3 := h4755c.2.2.2
                                linarith only [hlam, p4755_0]
                            · linarith only [h4272, h4686, h4754, hlam]
                          · linarith only [h4686, h4753, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h4687, h4752, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h4687, h4748, h4751, hlam]
                    · linarith only [h4686, h4750, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2808, h4272, h4748, h4749, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4799 | h4799
                  · linarith only [h0, h2808, h4564, h4748, h4799, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4801 | h4801
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4802 | h4802
                      · linarith only [h1106, h4748, h4802, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h4687, h4802, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h4686, h4801, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4806 | h4806
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4807 | h4807
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4808 | h4808
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4809 | h4809
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4810 | h4810
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4811 | h4811
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4812 | h4812
                      · linarith only [h0, h2808, h4272, h4806, h4812, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2808, h4806, h4809, h4812, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4815 | h4815
                      · linarith only [h0, h2808, h4272, h4806, h4815, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2808, h4809, h4811, h4815, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h2808, h4272, h4809, h4810, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4819 | h4819
                  · linarith only [h0, h2808, h4564, h4809, h4819, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4821 | h4821
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4822 | h4822
                      · linarith only [h1106, h4809, h4822, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4824 | h4824
                        · linarith only [h4806, h4819, h4824, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4826 | h4826
                          · linarith only [h0, h2808, h4272, h4686, h4807, h4826, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h3661, h4809, h4821, h4826, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4829 | h4829
                      · linarith only [h0, h2808, h4272, h4806, h4819, h4829, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4831 | h4831
                        · linarith only [h4806, h4819, h4831, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4833 | h4833
                          · linarith only [h1106, h4809, h4821, h4833, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4835 | h4835
                            · linarith only [h0, h2808, h4806, h4809, h4821, h4835, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h2808, h4806, h4809, h4835, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h2808, h4806, h4808, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2808, h4806, h4807, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4840 | h4840
            · linarith only [h0, h3661, h4806, h4840, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4842 | h4842
              · linarith only [h0, h4100, h4806, h4842, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4844 | h4844
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4845 | h4845
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4846 | h4846
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4847 | h4847
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4848 | h4848
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4849 | h4849
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4850 | h4850
                            · linarith only [h0, h2808, h4272, h4686, h4844, h4850, hc01, hc13, hlam, hphi]
                            · linarith only [h0, h2808, h4272, h4846, h4850, hc01, hc14, hlam, hphi]
                          · linarith only [h4840, h4846, h4849, hlam]
                        · linarith only [h4806, h4845, h4848, hlam]
                      · linarith only [h0, h2808, h4564, h4806, h4845, h4847, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4856 | h4856
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4857 | h4857
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4858 | h4858
                          · linarith only [h1991, h4846, h4858, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h4840, h4858, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h2808, h4845, h4857, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h2808, h4564, h4806, h4845, h4856, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2808, h4272, h4844, h4845, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4864 | h4864
                  · linarith only [h0, h2808, h4564, h4844, h4864, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4866 | h4866
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4867 | h4867
                      · linarith only [h1106, h4844, h4867, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h4806, h4867, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4870 | h4870
                      · linarith only [h0, h4806, h4844, h4870, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h4806, h4870, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2808 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 2 4 (by decide) (by decide) with h3661 | h3661
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991 h2494 h2808 h3661
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991 h2494 h2808 h3661

set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2494 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 2 3 (by decide) (by decide) with h2808 | h2808
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991 h2494 h2808
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991 h2494 h2808

set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1991 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 1 5 (by decide) (by decide) with h2494 | h2494
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991 h2494
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991 h2494

set_option maxHeartbeats 5764000 in
set_option maxHeartbeats 5764000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1106 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1106 := hg1106
  rcases m.htr 0 1 4 (by decide) (by decide) with h1991 | h1991
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x0 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s1_x1 m hb0 hb2 hb3 hb5 hg0 hg1106 h1991

end R2N4
