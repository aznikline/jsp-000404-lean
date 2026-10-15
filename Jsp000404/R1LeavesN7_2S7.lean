import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8760000 in
set_option maxHeartbeats 8760000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s7 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_10_12_23_L_I_L_I_H_I_s8 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4064 | h4064
    · linarith only [h4064, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4066 | h4066
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4067 | h4067
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4068 | h4068
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4069 | h4069
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4070 | h4070
              · linarith only [h1, h4070, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4072 | h4072
                · linarith only [h2, h4064, h4072, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4074 | h4074
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4075 | h4075
                    · linarith only [h1, h4066, h4075, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4077 | h4077
                      · linarith only [h4064, h4077, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4079 | h4079
                        · linarith only [h4064, h4068, h4074, h4075, h4079, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c | h4081c
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h0, h4068, h4074, h4075, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4081_1]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            rcases p4081_3 (m.d 0 1) (by simp) with h4084 | h4084
                            · rcases p4081_3 (m.d 0 2) (by simp) with h4085 | h4085
                              · linarith only [h0, h4085, hlam]
                              · linarith only [h4, h4085, hlam]
                            · linarith only [h1, h4084, hlam]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            rcases p4081_3 (m.d 0 1) (by simp) with h4089 | h4089
                            · rcases p4081_3 (m.d 0 2) (by simp) with h4090 | h4090
                              · linarith only [h0, h4090, hlam]
                              · linarith only [h4090, h5, hlam]
                            · linarith only [h2, h4089, hlam]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            rcases p4081_3 (m.d 0 1) (by simp) with h4094 | h4094
                            · rcases p4081_3 (m.d 0 2) (by simp) with h4095 | h4095
                              · linarith only [h0, h4095, hlam]
                              · linarith only [h4095, h6, hlam]
                            · linarith only [h3, h4094, hlam]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h0, hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            rcases p4081_3 (m.d 0 1) (by simp) with h4101 | h4101
                            · rcases p4081_3 (m.d 0 2) (by simp) with h4102 | h4102
                              · rcases p4081_3 (m.d 0 3) (by simp) with h4103 | h4103
                                · linarith only [h4, h4103, hlam]
                                · rcases p4081_3 (m.d 0 4) (by simp) with h4105 | h4105
                                  · linarith only [h4105, h5, hlam]
                                  · rcases p4081_3 (m.d 0 5) (by simp) with h4107 | h4107
                                    · linarith only [h4107, h6, hlam]
                                    · linarith only [h4107, h8, hlam]
                              · linarith only [h4, h4102, hlam]
                            · linarith only [h1, h4101, hlam]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            rcases p4081_3 (m.d 0 1) (by simp) with h4112 | h4112
                            · rcases p4081_3 (m.d 0 2) (by simp) with h4113 | h4113
                              · rcases p4081_3 (m.d 0 3) (by simp) with h4114 | h4114
                                · linarith only [h4, h4114, hlam]
                                · linarith only [h4114, h7, hlam]
                              · linarith only [h4113, h5, hlam]
                            · linarith only [h2, h4112, hlam]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            rcases p4081_3 (m.d 0 1) (by simp) with h4119 | h4119
                            · rcases p4081_3 (m.d 0 2) (by simp) with h4120 | h4120
                              · rcases p4081_3 (m.d 0 3) (by simp) with h4121 | h4121
                                · linarith only [h4, h4121, hlam]
                                · rcases p4081_3 (m.d 0 4) (by simp) with h4123 | h4123
                                  · linarith only [h4123, h5, hlam]
                                  · rcases p4081_3 (m.d 0 5) (by simp) with h4125 | h4125
                                    · linarith only [h4125, h6, hlam]
                                    · rcases h2bigk with h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c | h4127c
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h0, h4068, h4074, h4075, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        rcases p4127_3 (m.d 0 2) (by simp) with h4130 | h4130
                                        · rcases p4127_3 (m.d 1 2) (by simp) with h4131 | h4131
                                          · linarith only [h0, h4131, hlam]
                                          · linarith only [h4066, h4131, hlam]
                                        · linarith only [h4130, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        rcases p4127_3 (m.d 0 2) (by simp) with h4135 | h4135
                                        · rcases p4127_3 (m.d 1 2) (by simp) with h4136 | h4136
                                          · linarith only [h0, h4136, hlam]
                                          · linarith only [h4067, h4136, hlam]
                                        · linarith only [h4135, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        rcases p4127_3 (m.d 0 2) (by simp) with h4140 | h4140
                                        · rcases p4127_3 (m.d 1 2) (by simp) with h4141 | h4141
                                          · linarith only [h0, h4141, hlam]
                                          · linarith only [h4068, h4141, hlam]
                                        · linarith only [h4140, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h0, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h0, h4074, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        rcases p4127_3 (m.d 0 2) (by simp) with h4148 | h4148
                                        · rcases p4127_3 (m.d 1 2) (by simp) with h4149 | h4149
                                          · rcases p4127_3 (m.d 2 3) (by simp) with h4150 | h4150
                                            · linarith only [h4066, h4150, hlam]
                                            · linarith only [h4074, h4150, hlam]
                                          · linarith only [h4149, hlam, p4127_0]
                                        · linarith only [h4148, h5, hlam]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h0, h4074, h4075, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h4, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h4066, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h0, h4, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4081_1, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h4075, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h5, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h4067, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h4074, hlam, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h4077, hlam, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h6, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h4068, hlam, p4127_0]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4081_1, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [h0, h3, h4068, h4074, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4081_1, p4127_1]
                                      · have p4127_0 := h4127c.1
                                        have p4127_1 := h4127c.2.1
                                        have p4127_2 := h4127c.2.2.1
                                        have p4127_3 := h4127c.2.2.2
                                        linarith only [hlam, p4127_0]
                              · linarith only [h4120, h6, hlam]
                            · linarith only [h3, h4119, hlam]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h1, hlam, p4081_1]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h4, hlam, p4081_1]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h2, h4067, h4074, h4079, h8, hc34, hc45, hlam, hphi, p4081_1]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h8, hlam, p4081_1]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h2, hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h5, hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h7, hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h4064, hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h3, hlam, p4081_0]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h6, hlam, p4081_1]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [h4, h4074, h4079, h8, hc34, hc45, hlam, hphi, p4081_1]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            rcases p4081_3 (m.d 0 1) (by simp) with h4186 | h4186
                            · rcases p4081_3 (m.d 0 2) (by simp) with h4187 | h4187
                              · rcases p4081_3 (m.d 0 3) (by simp) with h4188 | h4188
                                · linarith only [h4188, h8, hlam]
                                · linarith only [h4188, h7, hlam]
                              · linarith only [h4187, h5, hlam]
                            · linarith only [h2, h4186, hlam]
                          · have p4081_0 := h4081c.1
                            have p4081_1 := h4081c.2.1
                            have p4081_2 := h4081c.2.2.1
                            have p4081_3 := h4081c.2.2.2
                            linarith only [hlam, p4081_0]
                  · linarith only [h4074, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h4069, h7, h8, hc13, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4196 | h4196
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4197 | h4197
              · linarith only [h1, h4197, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4199 | h4199
                · linarith only [h2, h4064, h4199, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4201 | h4201
                  · linarith only [h0, h4066, h4068, h4201, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h4201, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h4196, h7, h8, hc13, hc35, hlam, hphi]
        · linarith only [h4064, h4066, h4067, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4206 | h4206
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4207 | h4207
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4208 | h4208
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4209 | h4209
              · linarith only [h4, h4066, h4206, h4209, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h4066, h4207, h4209, hlam]
            · linarith only [h4066, h4206, h4208, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4213 | h4213
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4214 | h4214
              · linarith only [h1, h4214, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4216 | h4216
                · linarith only [h2, h4064, h4216, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4218 | h4218
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4219 | h4219
                    · linarith only [h4, h4219, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4221 | h4221
                      · linarith only [h2, h4064, h4206, h4221, h7, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4223 | h4223
                        · linarith only [h4, h4064, h4066, h4206, h4218, h4223, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h4, h4066, h4206, h4223, h8, hc24, hc45, hlam, hphi]
                  · linarith only [h4066, h4206, h4218, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h4066, h4206, h4213, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4228 | h4228
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4229 | h4229
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4230 | h4230
              · linarith only [h1, h4230, h8, hlam]
              · linarith only [h4066, h4228, h4230, hlam]
            · linarith only [h4066, h4229, h7, h8, hc12, hc35, hlam, hphi, ht23]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4234 | h4234
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4235 | h4235
              · linarith only [h1, h4235, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4237 | h4237
                · linarith only [h2, h4064, h4206, h4237, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4239 | h4239
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4240 | h4240
                    · linarith only [h4, h4240, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4242 | h4242
                      · linarith only [h4064, h4242, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4244 | h4244
                        · linarith only [h4064, h4206, h4244, h5, hc12, hc34, hlam, hphi, ht23]
                        · rcases h0bigk with h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c | h4246c
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h4228, h4234, h4235, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            rcases p4246_3 (m.d 0 1) (by simp) with h4249 | h4249
                            · rcases p4246_3 (m.d 0 2) (by simp) with h4250 | h4250
                              · linarith only [h0, h4250, hlam]
                              · linarith only [h4, h4250, hlam]
                            · linarith only [h1, h4249, hlam]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            rcases p4246_3 (m.d 0 1) (by simp) with h4254 | h4254
                            · rcases p4246_3 (m.d 0 2) (by simp) with h4255 | h4255
                              · linarith only [h0, h4255, hlam]
                              · linarith only [h4255, h5, hlam]
                            · linarith only [h2, h4254, hlam]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            rcases p4246_3 (m.d 0 1) (by simp) with h4259 | h4259
                            · rcases p4246_3 (m.d 0 2) (by simp) with h4260 | h4260
                              · linarith only [h0, h4260, hlam]
                              · linarith only [h4260, h6, hlam]
                            · linarith only [h3, h4259, hlam]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h0, hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            rcases p4246_3 (m.d 0 1) (by simp) with h4266 | h4266
                            · rcases p4246_3 (m.d 0 2) (by simp) with h4267 | h4267
                              · rcases p4246_3 (m.d 0 3) (by simp) with h4268 | h4268
                                · linarith only [h4, h4268, hlam]
                                · rcases p4246_3 (m.d 0 4) (by simp) with h4270 | h4270
                                  · linarith only [h4270, h5, hlam]
                                  · rcases p4246_3 (m.d 0 5) (by simp) with h4272 | h4272
                                    · linarith only [h4272, h6, hlam]
                                    · linarith only [h4272, h8, hlam]
                              · linarith only [h4, h4267, hlam]
                            · linarith only [h1, h4266, hlam]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            rcases p4246_3 (m.d 0 1) (by simp) with h4277 | h4277
                            · rcases p4246_3 (m.d 0 2) (by simp) with h4278 | h4278
                              · rcases p4246_3 (m.d 0 3) (by simp) with h4279 | h4279
                                · linarith only [h4, h4279, hlam]
                                · linarith only [h4279, h7, hlam]
                              · linarith only [h4278, h5, hlam]
                            · linarith only [h2, h4277, hlam]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            rcases p4246_3 (m.d 0 1) (by simp) with h4284 | h4284
                            · rcases p4246_3 (m.d 0 2) (by simp) with h4285 | h4285
                              · rcases p4246_3 (m.d 0 3) (by simp) with h4286 | h4286
                                · linarith only [h4, h4286, hlam]
                                · rcases p4246_3 (m.d 0 4) (by simp) with h4288 | h4288
                                  · linarith only [h4288, h5, hlam]
                                  · rcases p4246_3 (m.d 0 5) (by simp) with h4290 | h4290
                                    · linarith only [h4290, h6, hlam]
                                    · rcases h2bigk with h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c | h4292c
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4206, h5, h7, h8, hlam, p4246_1, p4292_2]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        rcases p4292_3 (m.d 0 2) (by simp) with h4295 | h4295
                                        · rcases p4292_3 (m.d 1 2) (by simp) with h4296 | h4296
                                          · linarith only [h0, h4296, hlam]
                                          · rcases p4292_3 (m.d 2 3) (by simp) with h4298 | h4298
                                            · linarith only [h4298, hlam, p4292_0]
                                            · rcases p4292_3 (m.d 2 4) (by simp) with h4300 | h4300
                                              · linarith only [h4300, h5, hlam]
                                              · rcases p4292_3 (m.d 2 5) (by simp) with h4302 | h4302
                                                · linarith only [h4302, h6, hlam]
                                                · linarith only [h4240, h4302, hlam]
                                        · linarith only [h4295, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        rcases p4292_3 (m.d 0 2) (by simp) with h4306 | h4306
                                        · rcases p4292_3 (m.d 1 2) (by simp) with h4307 | h4307
                                          · linarith only [h0, h4307, hlam]
                                          · rcases p4292_3 (m.d 2 3) (by simp) with h4309 | h4309
                                            · linarith only [h4, h4309, hlam]
                                            · linarith only [h4239, h4309, hlam]
                                        · linarith only [h4306, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        rcases p4292_3 (m.d 0 2) (by simp) with h4313 | h4313
                                        · rcases p4292_3 (m.d 1 2) (by simp) with h4314 | h4314
                                          · linarith only [h0, h4314, hlam]
                                          · rcases p4292_3 (m.d 2 3) (by simp) with h4316 | h4316
                                            · linarith only [h4, h4316, hlam]
                                            · rcases p4292_3 (m.d 2 4) (by simp) with h4318 | h4318
                                              · linarith only [h4318, h5, hlam]
                                              · rcases p4292_3 (m.d 2 5) (by simp) with h4320 | h4320
                                                · linarith only [h4320, hlam, p4292_0]
                                                · rcases h3bigk with h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c | h4322c
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4234, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4246_1, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h8, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4246_1, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4246_1, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h8, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h1, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4066, hlam, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4235, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4246_1, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4240, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h7, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4234, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4239, hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [hlam, p4322_0]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4244, hlam, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [hc03, hc35, hlam, hphi, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4234, h4244, hc34, hc45, hlam, hphi, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4206, h4239, h4244, hc12, hc45, hlam, hphi, ht23, ht34, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [h4244, hc34, hc45, hlam, hphi, p4322_1]
                                                  · have p4322_0 := h4322c.1
                                                    have p4322_1 := h4322c.2.1
                                                    have p4322_2 := h4322c.2.2.1
                                                    have p4322_3 := h4322c.2.2.2
                                                    linarith only [hlam, p4322_0]
                                        · linarith only [h4313, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4066, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4206, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4228, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h4240, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4246_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h4206, h4240, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4246_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4240, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h5, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4244, h5, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4239, hlam, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h4242, hlam, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h6, hlam, p4292_0]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4246_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4246_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [h0, h4206, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4246_1, p4292_1]
                                      · have p4292_0 := h4292c.1
                                        have p4292_1 := h4292c.2.1
                                        have p4292_2 := h4292c.2.2.1
                                        have p4292_3 := h4292c.2.2.2
                                        linarith only [hlam, p4292_0]
                              · linarith only [h4285, h6, hlam]
                            · linarith only [h3, h4284, hlam]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h1, hlam, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h4, hlam, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h4206, h4244, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h8, hlam, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h2, hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h5, hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h7, hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h4064, hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h3, hlam, p4246_0]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h6, hlam, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h1, h4234, h4244, h8, hc34, hc45, hlam, hphi, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [h4206, h4244, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4246_1]
                          · have p4246_0 := h4246c.1
                            have p4246_1 := h4246c.2.1
                            have p4246_2 := h4246c.2.2.1
                            have p4246_3 := h4246c.2.2.2
                            linarith only [hlam, p4246_0]
                  · linarith only [h1, h4234, h4239, h8, hc23, hc35, hlam, hphi]
            · linarith only [h4234, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  exact r1l7_10_12_23_L_I_L_I_H_I_s7 m hb0 hb2 hb3 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h4389 | h4389
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4390 | h4390
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4391 | h4391
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4392 | h4392
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4393 | h4393
          · linarith only [h1, h4393, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4395 | h4395
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4396 | h4396
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4397 | h4397
                · linarith only [h1, h4390, h4397, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4399 | h4399
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4400 | h4400
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4401 | h4401
                      · rcases h0bigk with h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c | h4402c
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h0, h4391, h4397, h4399, hc01, hc35, hlam, hphi, ht0b, ht5b, p4402_1]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4405 | h4405
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4406 | h4406
                            · linarith only [h0, h4406, hlam]
                            · linarith only [h4, h4406, hlam]
                          · linarith only [h1, h4405, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4410 | h4410
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4411 | h4411
                            · linarith only [h0, h4411, hlam]
                            · linarith only [h4411, h5, hlam]
                          · linarith only [h2, h4410, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4415 | h4415
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4416 | h4416
                            · linarith only [h0, h4416, hlam]
                            · linarith only [h4416, h6, hlam]
                          · linarith only [h3, h4415, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h0, hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4422 | h4422
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4423 | h4423
                            · rcases p4402_3 (m.d 0 3) (by simp) with h4424 | h4424
                              · linarith only [h4, h4424, hlam]
                              · rcases p4402_3 (m.d 0 4) (by simp) with h4426 | h4426
                                · linarith only [h4426, h5, hlam]
                                · linarith only [h4426, h7, hlam]
                            · linarith only [h4, h4423, hlam]
                          · linarith only [h1, h4422, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4431 | h4431
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4432 | h4432
                            · rcases p4402_3 (m.d 0 3) (by simp) with h4433 | h4433
                              · linarith only [h4, h4433, hlam]
                              · rcases p4402_3 (m.d 0 4) (by simp) with h4435 | h4435
                                · linarith only [h4435, h5, hlam]
                                · rcases p4402_3 (m.d 0 5) (by simp) with h4437 | h4437
                                  · linarith only [h4437, h6, hlam]
                                  · rcases h2bigk with h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c | h4439c
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4391, h4397, h4399, h4401, hc02, hc45, hlam, hphi, ht0b, ht5b, p4439_1]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      rcases p4439_3 (m.d 0 2) (by simp) with h4442 | h4442
                                      · rcases p4439_3 (m.d 1 2) (by simp) with h4443 | h4443
                                        · linarith only [h0, h4443, hlam]
                                        · linarith only [h4390, h4443, hlam]
                                      · linarith only [h4442, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      rcases p4439_3 (m.d 0 2) (by simp) with h4447 | h4447
                                      · rcases p4439_3 (m.d 1 2) (by simp) with h4448 | h4448
                                        · linarith only [h0, h4448, hlam]
                                        · linarith only [h4391, h4448, hlam]
                                      · linarith only [h4447, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      rcases p4439_3 (m.d 0 2) (by simp) with h4452 | h4452
                                      · rcases p4439_3 (m.d 1 2) (by simp) with h4453 | h4453
                                        · linarith only [h0, h4453, hlam]
                                        · linarith only [h4392, h4453, hlam]
                                      · linarith only [h4452, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h0, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h0, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4439_1]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h0, h4397, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4439_1]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      rcases p4439_3 (m.d 0 2) (by simp) with h4461 | h4461
                                      · rcases p4439_3 (m.d 1 2) (by simp) with h4462 | h4462
                                        · rcases p4439_3 (m.d 2 3) (by simp) with h4463 | h4463
                                          · linarith only [h4390, h4463, hlam]
                                          · linarith only [h4399, h4463, hlam]
                                        · linarith only [h4462, hlam, p4439_0]
                                      · linarith only [h4461, h6, hlam]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4390, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4397, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h0, h1, h4390, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p4402_1, p4439_1]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h5, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4391, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h0, h4399, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p4439_1]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h0, h2, h4391, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4402_1, p4439_1]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h6, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4392, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4399, hlam, p4439_1]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [h4400, hlam, p4439_0]
                                    · have p4439_0 := h4439c.1
                                      have p4439_1 := h4439c.2.1
                                      have p4439_2 := h4439c.2.2.1
                                      have p4439_3 := h4439c.2.2.2
                                      linarith only [hlam, p4439_0]
                            · linarith only [h4432, h5, hlam]
                          · linarith only [h2, h4431, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4485 | h4485
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4486 | h4486
                            · rcases p4402_3 (m.d 0 3) (by simp) with h4487 | h4487
                              · linarith only [h4, h4487, hlam]
                              · linarith only [h4388, h4487, hlam]
                            · linarith only [h4486, h6, hlam]
                          · linarith only [h3, h4485, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h1, hlam, p4402_1]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h4, hlam, p4402_1]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h7, hlam, p4402_1]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4496 | h4496
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4497 | h4497
                            · rcases p4402_3 (m.d 0 3) (by simp) with h4498 | h4498
                              · rcases p4402_3 (m.d 0 4) (by simp) with h4499 | h4499
                                · rcases p4402_3 (m.d 0 5) (by simp) with h4500 | h4500
                                  · linarith only [h4388, h4500, hlam]
                                  · rcases h2bigk with h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c | h4502c
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h0, h4390, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4502_1]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      rcases p4502_3 (m.d 0 2) (by simp) with h4505 | h4505
                                      · rcases p4502_3 (m.d 1 2) (by simp) with h4506 | h4506
                                        · linarith only [h0, h4506, hlam]
                                        · linarith only [h4390, h4506, hlam]
                                      · linarith only [h4505, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      rcases p4502_3 (m.d 0 2) (by simp) with h4510 | h4510
                                      · rcases p4502_3 (m.d 1 2) (by simp) with h4511 | h4511
                                        · linarith only [h0, h4511, hlam]
                                        · linarith only [h4391, h4511, hlam]
                                      · linarith only [h4510, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      rcases p4502_3 (m.d 0 2) (by simp) with h4515 | h4515
                                      · rcases p4502_3 (m.d 1 2) (by simp) with h4516 | h4516
                                        · linarith only [h0, h4516, hlam]
                                        · linarith only [h4392, h4516, hlam]
                                      · linarith only [h4515, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h0, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h0, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4502_1]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h0, h4397, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4502_1]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      rcases p4502_3 (m.d 0 2) (by simp) with h4524 | h4524
                                      · rcases p4502_3 (m.d 1 2) (by simp) with h4525 | h4525
                                        · rcases p4502_3 (m.d 2 3) (by simp) with h4526 | h4526
                                          · linarith only [h4390, h4526, hlam]
                                          · linarith only [h4399, h4526, hlam]
                                        · linarith only [h4525, hlam, p4502_0]
                                      · linarith only [h4524, h6, hlam]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h4, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h4390, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h4397, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h0, h4390, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4502_1]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h5, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h4391, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h0, h3, h4391, h4392, h4399, h4401, h7, hc01, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p4402_1, p4502_1]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h0, h4391, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4502_1]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h6, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h4392, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h4399, hlam, p4502_1]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [h4400, hlam, p4502_0]
                                    · have p4502_0 := h4502c.1
                                      have p4502_1 := h4502c.2.1
                                      have p4502_2 := h4502c.2.2.1
                                      have p4502_3 := h4502c.2.2.2
                                      linarith only [hlam, p4502_0]
                                · linarith only [h4389, h4499, hlam]
                              · linarith only [h4388, h4498, hlam]
                            · linarith only [h4497, h6, hlam]
                          · linarith only [h3, h4496, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h2, hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h5, hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4552 | h4552
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4553 | h4553
                            · rcases p4402_3 (m.d 0 3) (by simp) with h4554 | h4554
                              · linarith only [h4554, h7, hlam]
                              · rcases p4402_3 (m.d 0 4) (by simp) with h4556 | h4556
                                · rcases p4402_3 (m.d 0 5) (by simp) with h4557 | h4557
                                  · linarith only [h4389, h4557, hlam]
                                  · rcases h2bigk with h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h0, h4390, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4559_1]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      rcases p4559_3 (m.d 0 2) (by simp) with h4562 | h4562
                                      · rcases p4559_3 (m.d 1 2) (by simp) with h4563 | h4563
                                        · linarith only [h0, h4563, hlam]
                                        · linarith only [h4390, h4563, hlam]
                                      · linarith only [h4562, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      rcases p4559_3 (m.d 0 2) (by simp) with h4567 | h4567
                                      · rcases p4559_3 (m.d 1 2) (by simp) with h4568 | h4568
                                        · linarith only [h0, h4568, hlam]
                                        · linarith only [h4391, h4568, hlam]
                                      · linarith only [h4567, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      rcases p4559_3 (m.d 0 2) (by simp) with h4572 | h4572
                                      · rcases p4559_3 (m.d 1 2) (by simp) with h4573 | h4573
                                        · linarith only [h0, h4573, hlam]
                                        · linarith only [h4392, h4573, hlam]
                                      · linarith only [h4572, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h0, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h0, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4559_1]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h0, h4397, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4559_1]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      rcases p4559_3 (m.d 0 2) (by simp) with h4581 | h4581
                                      · rcases p4559_3 (m.d 1 2) (by simp) with h4582 | h4582
                                        · rcases p4559_3 (m.d 2 3) (by simp) with h4583 | h4583
                                          · linarith only [h4390, h4583, hlam]
                                          · linarith only [h4399, h4583, hlam]
                                        · linarith only [h4582, hlam, p4559_0]
                                      · linarith only [h4581, h6, hlam]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h4, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h4390, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h4397, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h1, h4390, h5, hc02, hc25, hlam, hphi, ht0b, ht5b, p4402_1, p4559_1]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h5, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h4391, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h0, h4391, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4559_1]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h0, h4391, h4399, h4401, hc01, hc45, hlam, hphi, ht0b, ht5b, p4559_1]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h6, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h4392, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h4399, hlam, p4559_1]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [h4400, hlam, p4559_0]
                                    · have p4559_0 := h4559c.1
                                      have p4559_1 := h4559c.2.1
                                      have p4559_2 := h4559c.2.2.1
                                      have p4559_3 := h4559c.2.2.2
                                      linarith only [hlam, p4559_0]
                                · linarith only [h4556, h7, hlam]
                            · linarith only [h4, h4553, hlam]
                          · linarith only [h1, h4552, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          rcases p4402_3 (m.d 0 1) (by simp) with h4607 | h4607
                          · rcases p4402_3 (m.d 0 2) (by simp) with h4608 | h4608
                            · rcases p4402_3 (m.d 0 3) (by simp) with h4609 | h4609
                              · linarith only [h4609, h7, hlam]
                              · linarith only [h4388, h4609, hlam]
                            · linarith only [h4608, h6, hlam]
                          · linarith only [h3, h4607, hlam]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h3, hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h6, hlam, p4402_1]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h4388, hlam, p4402_0]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [h4389, hlam, p4402_1]
                        · have p4402_0 := h4402c.1
                          have p4402_1 := h4402c.2.1
                          have p4402_2 := h4402c.2.2.1
                          have p4402_3 := h4402c.2.2.2
                          linarith only [hlam, p4402_0]
                      · linarith only [h4389, h4401, h7, hlam]
                    · linarith only [h2, h4396, h4397, h4399, h4400, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4388, h4399, h7, hc23, hc34, hlam, hphi]
              · linarith only [h4393, h4395, h4396, hlam]
            · linarith only [h4388, h4395, h7, hc13, hc34, hlam, hphi]
        · linarith only [h4388, h4390, h4392, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4625 | h4625
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4626 | h4626
          · linarith only [h1, h4388, h4626, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4628 | h4628
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4629 | h4629
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4630 | h4630
                · linarith only [h4390, h4391, h4630, h5, h7, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4632 | h4632
                  · linarith only [h0, h4390, h4391, h4632, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h4628, h4632, h7, hc23, hc34, hlam, hphi]
              · linarith only [h4388, h4389, h4390, h4391, h4629, h7, hc23, hc34, hlam, hphi]
            · linarith only [h4388, h4628, h7, hc13, hc34, hlam, hphi]
        · linarith only [h4388, h4390, h4625, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4638 | h4638
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4639 | h4639
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4640 | h4640
          · linarith only [h4, h4388, h4390, h4640, h7, hc02, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h4390, h4638, h4640, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4643 | h4643
          · linarith only [h4388, h4638, h4639, h4643, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h4390, h4638, h4643, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4646 | h4646
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4647 | h4647
          · linarith only [h4, h4390, h4646, h4647, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4649 | h4649
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4650 | h4650
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4651 | h4651
                · linarith only [h4, h4651, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4653 | h4653
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4654 | h4654
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4655 | h4655
                      · rcases h0bigk with h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c | h4656c
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h4390, h4646, h4651, h4653, h4655, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h4, h4390, h4646, h4653, h4655, hc01, hc45, hlam, hphi, ht0b, ht5b, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h4, h4390, h4646, h4653, h4655, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          rcases p4656_3 (m.d 0 1) (by simp) with h4661 | h4661
                          · rcases p4656_3 (m.d 0 2) (by simp) with h4662 | h4662
                            · linarith only [h0, h4662, hlam]
                            · linarith only [h4662, h6, hlam]
                          · linarith only [h3, h4661, hlam]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h0, hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h4, h4390, h4646, h4653, h4655, hc02, hc45, hlam, hphi, ht0b, ht5b, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h0, h4, h4390, h4646, h4653, h4655, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          rcases p4656_3 (m.d 0 1) (by simp) with h4670 | h4670
                          · rcases p4656_3 (m.d 0 2) (by simp) with h4671 | h4671
                            · rcases p4656_3 (m.d 0 3) (by simp) with h4672 | h4672
                              · linarith only [h4, h4672, hlam]
                              · linarith only [h4388, h4672, hlam]
                            · linarith only [h4671, h6, hlam]
                          · linarith only [h3, h4670, hlam]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h1, hlam, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h4, hlam, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h7, hlam, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          rcases p4656_3 (m.d 0 1) (by simp) with h4681 | h4681
                          · rcases p4656_3 (m.d 0 2) (by simp) with h4682 | h4682
                            · rcases p4656_3 (m.d 0 3) (by simp) with h4683 | h4683
                              · rcases p4656_3 (m.d 0 4) (by simp) with h4684 | h4684
                                · rcases p4656_3 (m.d 0 5) (by simp) with h4685 | h4685
                                  · linarith only [h4388, h4685, hlam]
                                  · rcases h2bigk with h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c | h4687c
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      rcases p4687_3 (m.d 0 2) (by simp) with h4689 | h4689
                                      · rcases p4687_3 (m.d 1 2) (by simp) with h4690 | h4690
                                        · linarith only [h0, h4690, hlam]
                                        · rcases p4687_3 (m.d 2 3) (by simp) with h4692 | h4692
                                          · linarith only [h4, h4692, hlam]
                                          · linarith only [h4390, h4692, hlam]
                                      · linarith only [h0, h4689, hlam]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h0, h4390, h4646, h4653, h4655, hc01, hc45, hlam, hphi, ht0b, ht5b, p4687_1]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h0, h4390, h4646, h4651, h4653, h4655, hc01, hc45, hlam, hphi, ht0b, ht5b, p4687_1]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4, h4390, h4646, hlam, p4687_2]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h0, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4390, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4638, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4, h4390, h4653, h4655, hc02, hc45, hlam, hphi, ht0b, ht5b, p4687_1]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p4687_1]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4651, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      rcases p4687_3 (m.d 0 2) (by simp) with h4708 | h4708
                                      · rcases p4687_3 (m.d 1 2) (by simp) with h4709 | h4709
                                        · linarith only [h4390, h4709, hlam]
                                        · linarith only [h4646, h4709, hlam]
                                      · linarith only [h4708, h6, hlam]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h5, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h0, h4646, h4653, h4655, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4687_1]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h0, h4390, h4646, h4653, h4655, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4687_1]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      rcases p4687_3 (m.d 0 2) (by simp) with h4717 | h4717
                                      · rcases p4687_3 (m.d 1 2) (by simp) with h4718 | h4718
                                        · linarith only [h4638, h4718, hlam]
                                        · linarith only [h4646, h4718, hlam]
                                      · linarith only [h4717, h6, hlam]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h6, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4646, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4653, hlam, p4687_1]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [h4654, hlam, p4687_0]
                                    · have p4687_0 := h4687c.1
                                      have p4687_1 := h4687c.2.1
                                      have p4687_2 := h4687c.2.2.1
                                      have p4687_3 := h4687c.2.2.2
                                      linarith only [hlam, p4687_0]
                                · linarith only [h4389, h4684, hlam]
                              · linarith only [h4388, h4683, hlam]
                            · linarith only [h4682, h6, hlam]
                          · linarith only [h3, h4681, hlam]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h2, hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h5, hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h2, h4, h4390, h4646, h4653, h4655, hc01, hc45, hlam, hphi, ht0b, ht5b, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          rcases p4656_3 (m.d 0 1) (by simp) with h4735 | h4735
                          · rcases p4656_3 (m.d 0 2) (by simp) with h4736 | h4736
                            · rcases p4656_3 (m.d 0 3) (by simp) with h4737 | h4737
                              · linarith only [h4737, h7, hlam]
                              · linarith only [h4388, h4737, hlam]
                            · linarith only [h4736, h6, hlam]
                          · linarith only [h3, h4735, hlam]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h3, hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h6, hlam, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h4388, hlam, p4656_0]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [h4389, hlam, p4656_1]
                        · have p4656_0 := h4656c.1
                          have p4656_1 := h4656c.2.1
                          have p4656_2 := h4656c.2.2.1
                          have p4656_3 := h4656c.2.2.2
                          linarith only [hlam, p4656_0]
                      · linarith only [h4, h4390, h4655, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h3, h4638, h4646, h4650, h4653, h4654, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4388, h4390, h4646, h4653, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h4390, h4646, h4647, h4650, hlam]
            · linarith only [h4388, h4390, h4649, h7, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4752 | h4752
          · linarith only [h1, h4388, h4752, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4754 | h4754
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4755 | h4755
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4756 | h4756
                · linarith only [h4, h4756, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4758 | h4758
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4759 | h4759
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4760 | h4760
                      · rcases h0bigk with h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c | h4761c
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4646, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          rcases p4761_3 (m.d 0 1) (by simp) with h4764 | h4764
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4765 | h4765
                            · linarith only [h0, h4765, hlam]
                            · linarith only [h4, h4765, hlam]
                          · linarith only [h1, h4764, hlam]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          rcases p4761_3 (m.d 0 1) (by simp) with h4769 | h4769
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4770 | h4770
                            · linarith only [h0, h4770, hlam]
                            · linarith only [h4770, h5, hlam]
                          · linarith only [h2, h4769, hlam]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          rcases p4761_3 (m.d 0 1) (by simp) with h4774 | h4774
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4775 | h4775
                            · linarith only [h0, h4775, hlam]
                            · linarith only [h4775, h6, hlam]
                          · linarith only [h3, h4774, hlam]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h0, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          rcases p4761_3 (m.d 0 1) (by simp) with h4781 | h4781
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4782 | h4782
                            · rcases p4761_3 (m.d 0 3) (by simp) with h4783 | h4783
                              · linarith only [h4, h4783, hlam]
                              · rcases p4761_3 (m.d 0 4) (by simp) with h4785 | h4785
                                · linarith only [h4785, h5, hlam]
                                · linarith only [h4785, h7, hlam]
                            · linarith only [h4, h4782, hlam]
                          · linarith only [h1, h4781, hlam]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          rcases p4761_3 (m.d 0 1) (by simp) with h4790 | h4790
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4791 | h4791
                            · rcases p4761_3 (m.d 0 3) (by simp) with h4792 | h4792
                              · linarith only [h4, h4792, hlam]
                              · rcases p4761_3 (m.d 0 4) (by simp) with h4794 | h4794
                                · linarith only [h4794, h5, hlam]
                                · rcases p4761_3 (m.d 0 5) (by simp) with h4796 | h4796
                                  · linarith only [h4796, h6, hlam]
                                  · rcases h2bigk with h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c | h4798c
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4646, h4756, h4758, h5, hlam, p4761_1, p4798_2]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      rcases p4798_3 (m.d 0 2) (by simp) with h4801 | h4801
                                      · rcases p4798_3 (m.d 1 2) (by simp) with h4802 | h4802
                                        · linarith only [h0, h4802, hlam]
                                        · rcases p4798_3 (m.d 2 3) (by simp) with h4804 | h4804
                                          · linarith only [h4804, hlam, p4798_0]
                                          · rcases p4798_3 (m.d 2 4) (by simp) with h4806 | h4806
                                            · linarith only [h4806, h5, hlam]
                                            · linarith only [h4756, h4806, hlam]
                                      · linarith only [h4801, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      rcases p4798_3 (m.d 0 2) (by simp) with h4810 | h4810
                                      · rcases p4798_3 (m.d 1 2) (by simp) with h4811 | h4811
                                        · linarith only [h0, h4811, hlam]
                                        · rcases p4798_3 (m.d 2 3) (by simp) with h4813 | h4813
                                          · linarith only [h4, h4813, hlam]
                                          · rcases p4798_3 (m.d 2 4) (by simp) with h4815 | h4815
                                            · linarith only [h4815, hlam, p4798_0]
                                            · rcases p4798_3 (m.d 2 5) (by simp) with h4817 | h4817
                                              · linarith only [h4817, h6, hlam]
                                              · rcases h3bigk with h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c | h4819c
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h7, hc13, hc34, hlam, hphi, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4646, h4758, h7, hc12, hc34, hlam, hphi, ht23, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h7, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4760, h7, hc02, hc45, hlam, hphi, ht0b, ht5b, p4761_1, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h1, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4390, hlam, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4752, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h1, h4760, hc01, hc45, hlam, hphi, ht0b, ht5b, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4756, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h0, h4, h4760, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p4761_1, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [hc03, hc34, hlam, hphi, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4754, h4760, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4390, hc12, hc34, hlam, hphi, ht23, p4819_1]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  rcases p4819_3 (m.d 0 3) (by simp) with h4839 | h4839
                                                  · linarith only [h4839, h7, hlam]
                                                  · linarith only [h4388, h4839, hlam]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4388, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4754, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4758, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [h4760, hlam, p4819_0]
                                                · have p4819_0 := h4819c.1
                                                  have p4819_1 := h4819c.2.1
                                                  have p4819_2 := h4819c.2.2.1
                                                  have p4819_3 := h4819c.2.2.2
                                                  linarith only [hlam, p4819_0]
                                      · linarith only [h4810, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      rcases p4798_3 (m.d 0 2) (by simp) with h4848 | h4848
                                      · rcases p4798_3 (m.d 1 2) (by simp) with h4849 | h4849
                                        · linarith only [h0, h4849, hlam]
                                        · rcases p4798_3 (m.d 2 3) (by simp) with h4851 | h4851
                                          · linarith only [h4, h4851, hlam]
                                          · linarith only [h4758, h4851, hlam]
                                      · linarith only [h4848, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h0, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4390, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4638, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4646, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h0, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4761_1, p4798_1]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4756, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h0, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p4761_1, p4798_1]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h5, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4761_1, p4798_1]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4761_1, p4798_1]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h0, h4646, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4761_1, p4798_1]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h6, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h0, h4, h4758, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4761_1, p4798_1]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4758, hlam, p4798_1]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [h4759, hlam, p4798_0]
                                    · have p4798_0 := h4798c.1
                                      have p4798_1 := h4798c.2.1
                                      have p4798_2 := h4798c.2.2.1
                                      have p4798_3 := h4798c.2.2.2
                                      linarith only [hlam, p4798_0]
                            · linarith only [h4791, h5, hlam]
                          · linarith only [h2, h4790, hlam]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          rcases p4761_3 (m.d 0 1) (by simp) with h4877 | h4877
                          · rcases p4761_3 (m.d 0 2) (by simp) with h4878 | h4878
                            · rcases p4761_3 (m.d 0 3) (by simp) with h4879 | h4879
                              · linarith only [h4, h4879, hlam]
                              · linarith only [h4388, h4879, hlam]
                            · linarith only [h4878, h6, hlam]
                          · linarith only [h3, h4877, hlam]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h1, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h7, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h3, h4646, h7, hc12, hc34, hlam, hphi, ht23, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h2, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h5, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4, h4390, h7, hc12, hc34, hlam, hphi, ht23, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4646, h6, h7, hc12, hc34, hlam, hphi, ht23, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h3, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h6, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4388, hlam, p4761_0]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [h4389, hlam, p4761_1]
                        · have p4761_0 := h4761c.1
                          have p4761_1 := h4761c.2.1
                          have p4761_2 := h4761c.2.2.1
                          have p4761_3 := h4761c.2.2.2
                          linarith only [hlam, p4761_0]
                      · linarith only [h4388, h4646, h4760, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h3, h4388, h4638, h4755, h4759, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h4390, h4754, h4758, hlam]
              · linarith only [h4752, h4754, h4755, hlam]
            · linarith only [h4388, h4754, h7, hc13, hc34, hlam, hphi]
  · linarith only [h4388, h4389, h7, hlam]

end R2N4
