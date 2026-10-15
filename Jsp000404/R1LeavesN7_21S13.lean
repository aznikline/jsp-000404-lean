import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S5
import Jsp000404.R1LeavesN7_21S10
import Jsp000404.R1LeavesN7_21S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4072 | h4072
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4073 | h4073
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4074 | h4074
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4075 | h4075
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4076 | h4076
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4077 | h4077
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4078 | h4078
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4079 | h4079
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4080 | h4080
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4081 | h4081
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4082 | h4082
                      · linarith only [h2859, h4072, h4076, h4082, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h2859, h4072, h4075, h4076, h4082, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h2859, h4074, h4081, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h2859, h4072, h4080, hlam]
                · linarith only [h2859, h4072, h4075, h4076, h4079, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h2859, h4076, h4078, hc02, hc25, hlam, hphi]
            · linarith only [h2859, h4072, h4076, h4077, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4090 | h4090
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4091 | h4091
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4092 | h4092
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4093 | h4093
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4094 | h4094
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4095 | h4095
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4096 | h4096
                        · rcases h2bigk with h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c | h4097c
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
                            linarith only [h2859, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4093, h4096, hc45, hlam, hphi, ht0b, ht5b, p4097_1, u0elo1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            rcases p4097_3 (m.d 0 2) (by simp) with h4102 | h4102
                            · rcases p4097_3 (m.d 1 2) (by simp) with h4103 | h4103
                              · rcases p4097_3 (m.d 2 3) (by simp) with h4104 | h4104
                                · rcases p4097_3 (m.d 2 4) (by simp) with h4105 | h4105
                                  · linarith only [h4072, h4105, hlam]
                                  · linarith only [h4095, h4105, hlam]
                                · linarith only [h4094, h4104, hlam]
                              · linarith only [h4091, h4103, hlam]
                            · linarith only [h4102, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4072, h4093, h4096, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4097_1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4076, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4076, h4093, h4096, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4097_1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            rcases p4097_3 (m.d 0 2) (by simp) with h4115 | h4115
                            · linarith only [h0, h4115, hlam]
                            · linarith only [h4073, h4115, hlam]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4072, h4093, h4096, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4097_1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h0, h2858, h4091, h4094, h4096, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4097_1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            rcases p4097_3 (m.d 0 2) (by simp) with h4121 | h4121
                            · linarith only [h2859, h4121, hlam]
                            · linarith only [h4072, h4121, hlam]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h0, h2858, h4076, h4091, hlam, p4097_2]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4072, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4090, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4093, hlam, p4097_1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4072, h4094, h4096, hc45, hlam, hphi, ht0b, ht5b, p4097_1, u0elo1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4073, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4091, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4094, hlam, p4097_1]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [h4095, hlam, p4097_0]
                          · have p4097_0 := h4097c.1
                            have p4097_1 := h4097c.2.1
                            have p4097_2 := h4097c.2.2.1
                            have p4097_3 := h4097c.2.2.2
                            linarith only [hlam, p4097_0]
                        · linarith only [h0, h2858, h4076, h4092, h4096, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h2858, h4076, h4092, h4095, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h4076, h4094, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2858, h4076, h4091, h4093, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4139 | h4139
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4140 | h4140
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4141 | h4141
                      · linarith only [h4090, h4092, h4141, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4143 | h4143
                        · linarith only [h4090, h4092, h4139, h4143, hlam]
                        · rcases h2bigk with h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h0, hlam, p4145_1]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h2859, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            rcases p4145_3 (m.d 0 2) (by simp) with h4149 | h4149
                            · rcases p4145_3 (m.d 1 2) (by simp) with h4150 | h4150
                              · rcases p4145_3 (m.d 2 3) (by simp) with h4151 | h4151
                                · rcases p4145_3 (m.d 2 4) (by simp) with h4152 | h4152
                                  · linarith only [h4152, hlam, p4145_0]
                                  · rcases p4145_3 (m.d 2 5) (by simp) with h4154 | h4154
                                    · linarith only [h4073, h4154, hlam]
                                    · linarith only [h4141, h4154, hlam]
                                · linarith only [h4139, h4151, hlam]
                              · linarith only [h4090, h4150, hlam]
                            · linarith only [h4149, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            rcases p4145_3 (m.d 0 2) (by simp) with h4160 | h4160
                            · rcases p4145_3 (m.d 1 2) (by simp) with h4161 | h4161
                              · rcases p4145_3 (m.d 2 3) (by simp) with h4162 | h4162
                                · rcases p4145_3 (m.d 2 4) (by simp) with h4163 | h4163
                                  · linarith only [h4072, h4163, hlam]
                                  · rcases p4145_3 (m.d 2 5) (by simp) with h4165 | h4165
                                    · linarith only [h4165, hlam, p4145_0]
                                    · rcases h5bigk with h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c | h4167c
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h2858, h4090, h4092, h4139, hc34, hlam, hphi, ht0b, ht45, ht5b, p4167_1, u0elo0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h2858, h4139, h4141, hc34, hlam, hphi, ht0b, ht45, ht5b, p4167_1, u0elo0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h0, h2858, h4076, h4143, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h0, h2858, h4076, h4090, h4092, h4139, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h2858, hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h0, h2858, h4076, h4139, h4141, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h0, h2858, h4076, h4143, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4092, hlam, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4073, hlam, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4091, hlam, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4143, hc34, hlam, hphi, ht0b, ht45, ht5b, p4145_1, p4167_1, u0elo1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4141, hlam, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4074, hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4074, hc15, hlam, hphi, ht0b, ht5b, p4167_1, u0elo2]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4140, hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4143, hlam, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4075, hlam, p4167_0]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h4075, hc15, hlam, hphi, ht0b, ht5b, p4167_1, u0elo3]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h0, h4072, h4075, h4076, h4140, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [h0, h4072, h4075, h4076, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p4167_1]
                                      · have p4167_0 := h4167c.1
                                        have p4167_1 := h4167c.2.1
                                        have p4167_2 := h4167c.2.2.1
                                        have p4167_3 := h4167c.2.2.2
                                        linarith only [hlam, p4167_0]
                                · linarith only [h4140, h4162, hlam]
                              · linarith only [h4091, h4161, hlam]
                            · linarith only [h4160, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4076, hc02, hc23, hlam, hphi, p4145_1]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4076, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            rcases p4145_3 (m.d 0 2) (by simp) with h4199 | h4199
                            · linarith only [h0, h4199, hlam]
                            · linarith only [h4072, h4199, hlam]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            rcases p4145_3 (m.d 0 2) (by simp) with h4202 | h4202
                            · linarith only [h0, h4202, hlam]
                            · linarith only [h4073, h4202, hlam]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4072, h4075, h4090, h4092, h4139, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4145_1]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4145_1]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h2859, h4072, h4075, h4090, h4092, hlam, p4145_2]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h0, h2858, h4076, h4091, hlam, p4145_2]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4072, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4090, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4139, hlam, p4145_1]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4141, hlam, p4145_1]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4073, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4091, hlam, p4145_0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h4140, hlam, p4145_1]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [h2858, h4091, h4139, hc34, hlam, hphi, ht0b, ht45, ht5b, p4145_1, u0elo0]
                          · have p4145_0 := h4145c.1
                            have p4145_1 := h4145c.2.1
                            have p4145_2 := h4145c.2.2.1
                            have p4145_3 := h4145c.2.2.2
                            linarith only [hlam, p4145_0]
                    · linarith only [h0, h4076, h4140, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h4072, h4075, h4076, h4092, h4139, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h0, h2858, h4073, h4091, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
            · linarith only [h0, h4072, h4090, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4224 | h4224
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4225 | h4225
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4226 | h4226
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4227 | h4227
                · linarith only [h0, h2858, h2859, h4075, h4224, h4227, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4229 | h4229
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4230 | h4230
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4231 | h4231
                      · linarith only [h0, h2858, h2859, h4075, h4224, h4225, h4227, h4231, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4233 | h4233
                        · linarith only [h2858, h2859, h4072, h4075, h4224, h4227, h4229, h4233, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h2bigk with h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c | h4235c
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h2859, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h2859, h4224, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h2859, h4224, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            rcases p4235_3 (m.d 0 2) (by simp) with h4241 | h4241
                            · linarith only [h0, h4241, hlam]
                            · rcases p4235_3 (m.d 1 2) (by simp) with h4243 | h4243
                              · rcases p4235_3 (m.d 2 3) (by simp) with h4244 | h4244
                                · linarith only [h4224, h4244, hlam]
                                · linarith only [h2859, h4244, hlam]
                              · linarith only [h0, h4243, hlam]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h0, h2859, hc01, hc12, hlam, hphi, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h2859, h4072, h4224, hlam, p4235_2]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h2859, h4073, h4224, hlam, p4235_2]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4073, h4224, h4230, h4233, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4224, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            rcases p4235_3 (m.d 0 2) (by simp) with h4255 | h4255
                            · linarith only [h2859, h4255, hlam]
                            · linarith only [h4072, h4255, hlam]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            rcases p4235_3 (m.d 0 2) (by simp) with h4258 | h4258
                            · linarith only [h2859, h4258, hlam]
                            · linarith only [h4073, h4258, hlam]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4072, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4225, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4229, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4231, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4073, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4226, hlam, p4235_0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h4230, hlam, p4235_1]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [h2858, h4226, hc24, hlam, hphi, ht0b, ht45, ht5b, p4235_1, u0elo0]
                          · have p4235_0 := h4235c.1
                            have p4235_1 := h4235c.2.1
                            have p4235_2 := h4235c.2.2.1
                            have p4235_3 := h4235c.2.2.2
                            linarith only [hlam, p4235_0]
                    · linarith only [h2859, h4074, h4230, hlam]
                  · linarith only [h2859, h4072, h4229, hlam]
              · linarith only [h0, h2859, h4224, h4226, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h2858, h2859, h4072, h4224, h4225, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4275 | h4275
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4276 | h4276
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4277 | h4277
                · linarith only [h0, h2858, h4072, h4075, h4224, h4277, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4279 | h4279
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4280 | h4280
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4281 | h4281
                      · linarith only [h4072, h4075, h4281, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4283 | h4283
                        · linarith only [h0, h2858, h4075, h4224, h4275, h4277, h4279, h4283, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases h2bigk with h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c | h4285c
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h0, hlam, p4285_1]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h2859, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            rcases p4285_3 (m.d 0 2) (by simp) with h4289 | h4289
                            · rcases p4285_3 (m.d 1 2) (by simp) with h4290 | h4290
                              · rcases p4285_3 (m.d 2 3) (by simp) with h4291 | h4291
                                · rcases p4285_3 (m.d 2 4) (by simp) with h4292 | h4292
                                  · linarith only [h4292, hlam, p4285_0]
                                  · rcases p4285_3 (m.d 2 5) (by simp) with h4294 | h4294
                                    · linarith only [h4073, h4294, hlam]
                                    · linarith only [h4281, h4294, hlam]
                                · linarith only [h4279, h4291, hlam]
                              · linarith only [h4275, h4290, hlam]
                            · linarith only [h4289, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            rcases p4285_3 (m.d 0 2) (by simp) with h4300 | h4300
                            · rcases p4285_3 (m.d 1 2) (by simp) with h4301 | h4301
                              · rcases p4285_3 (m.d 2 3) (by simp) with h4302 | h4302
                                · rcases p4285_3 (m.d 2 4) (by simp) with h4303 | h4303
                                  · linarith only [h4072, h4303, hlam]
                                  · rcases p4285_3 (m.d 2 5) (by simp) with h4305 | h4305
                                    · linarith only [h4305, hlam, p4285_0]
                                    · rcases h5bigk with h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c | h4307c
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [hlam, p4307_0]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4277, hc14, hlam, hphi, ht0b, ht45, ht5b, p4307_1, u0elo4]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h0, h2858, h4224, h4281, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h0, h2858, h4224, h4283, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4075, hlam, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h2858, hlam, p4307_0]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [hlam, p4307_0]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h0, h2858, h4224, h4281, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h0, h2858, h4224, h4283, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4277, hlam, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4073, hlam, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4276, hlam, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [hlam, p4307_0]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4283, hc34, hlam, hphi, ht0b, ht45, ht5b, p4285_1, p4307_1, u0elo1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4281, hlam, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4074, hlam, p4307_0]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4074, hc15, hlam, hphi, ht0b, ht5b, p4307_1, u0elo2]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4280, hlam, p4307_0]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [hlam, p4307_0]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4283, hlam, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4072, h4075, h4279, hc34, hc45, hlam, hphi, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4275, h4277, h4279, hc34, hc45, hlam, hphi, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4279, h4281, hc34, hc45, hlam, hphi, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [h4283, hc34, hc45, hlam, hphi, p4307_1]
                                      · have p4307_0 := h4307c.1
                                        have p4307_1 := h4307c.2.1
                                        have p4307_2 := h4307c.2.2.1
                                        have p4307_3 := h4307c.2.2.2
                                        linarith only [hlam, p4307_0]
                                · linarith only [h4280, h4302, hlam]
                              · linarith only [h4276, h4301, hlam]
                            · linarith only [h4300, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4224, hc02, hc23, hlam, hphi, p4285_1]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4224, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            rcases p4285_3 (m.d 0 2) (by simp) with h4339 | h4339
                            · linarith only [h0, h4339, hlam]
                            · linarith only [h4072, h4339, hlam]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            rcases p4285_3 (m.d 0 2) (by simp) with h4342 | h4342
                            · linarith only [h0, h4342, hlam]
                            · linarith only [h4073, h4342, hlam]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            rcases p4285_3 (m.d 0 2) (by simp) with h4345 | h4345
                            · linarith only [h4345, hlam, p4285_0]
                            · rcases p4285_3 (m.d 1 2) (by simp) with h4347 | h4347
                              · linarith only [h4224, h4347, hlam]
                              · linarith only [h0, h4347, hlam]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h0, h2858, h4275, h4277, h4279, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4285_1]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h0, h2858, h4224, h4275, h4277, hlam, p4285_2]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h0, h2858, h4224, h4276, hlam, p4285_2]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4072, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4275, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4279, hlam, p4285_1]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4281, hlam, p4285_1]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4073, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4276, hlam, p4285_0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h4280, hlam, p4285_1]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [h2858, h4276, h4279, hc34, hlam, hphi, ht0b, ht45, ht5b, p4285_1, u0elo0]
                          · have p4285_0 := h4285c.1
                            have p4285_1 := h4285c.2.1
                            have p4285_2 := h4285c.2.2.1
                            have p4285_3 := h4285c.2.2.2
                            linarith only [hlam, p4285_0]
                    · linarith only [h0, h4224, h4280, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h2858, h4224, h4275, h4277, h4279, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · linarith only [h0, h4073, h4276, hlam]
            · linarith only [h0, h2858, h4072, h4275, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
      · linarith only [h0, h2858, h2859, h4074, hlam]
    · linarith only [h0, h2858, h4073, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4370 | h4370
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4371 | h4371
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4372 | h4372
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4373 | h4373
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4374 | h4374
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4375 | h4375
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4376 | h4376
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4377 | h4377
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4378 | h4378
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4379 | h4379
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4380 | h4380
                        · rcases h2bigk with h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c | h4381c
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h0, hlam, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h2859, hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4072, hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h2859, h4373, h4378, h4380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            rcases p4381_3 (m.d 0 2) (by simp) with h4387 | h4387
                            · linarith only [h0, h4387, hlam]
                            · rcases p4381_3 (m.d 1 2) (by simp) with h4389 | h4389
                              · rcases p4381_3 (m.d 2 3) (by simp) with h4390 | h4390
                                · linarith only [h4373, h4390, hlam]
                                · linarith only [h2859, h4390, hlam]
                              · linarith only [h0, h4389, hlam]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h0, h2858, h4072, h4375, h4377, h4378, h4380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h0, h2858, h4072, h4375, h4378, h4380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h0, h2858, h4072, h4373, h4375, h4377, hlam, p4381_2]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h0, h2858, h4373, h4375, h4378, h4380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4373, hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h0, h2858, h4072, h4373, h4375, h4378, h4380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            rcases p4381_3 (m.d 0 2) (by simp) with h4402 | h4402
                            · linarith only [h2859, h4402, hlam]
                            · linarith only [h4370, h4402, hlam]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h0, h2858, h4374, h4375, h4378, h4380, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4374, hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4377, hlam, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            rcases p4381_3 (m.d 0 2) (by simp) with h4409 | h4409
                            · linarith only [h4072, h4409, hlam]
                            · linarith only [h4370, h4409, hlam]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4370, hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4375, hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4378, hlam, p4381_1]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [h4379, hlam, p4381_0]
                          · have p4381_0 := h4381c.1
                            have p4381_1 := h4381c.2.1
                            have p4381_2 := h4381c.2.2.1
                            have p4381_3 := h4381c.2.2.2
                            linarith only [hlam, p4381_0]
                        · linarith only [h0, h2858, h4072, h4373, h4376, h4377, h4380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h2858, h4072, h4376, h4379, hlam]
                    · linarith only [h0, h4072, h4371, h4377, h4378, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4420 | h4420
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4421 | h4421
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4422 | h4422
                        · rcases h2bigk with h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c | h4423c
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h0, hlam, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h2859, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4072, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h2859, h4377, h4420, h4422, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            rcases p4423_3 (m.d 0 2) (by simp) with h4429 | h4429
                            · linarith only [h0, h4429, hlam]
                            · rcases p4423_3 (m.d 1 2) (by simp) with h4431 | h4431
                              · rcases p4423_3 (m.d 2 3) (by simp) with h4432 | h4432
                                · linarith only [h4373, h4432, hlam]
                                · linarith only [h2859, h4432, hlam]
                              · linarith only [h0, h4431, hlam]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h0, h2858, h2859, h4375, h4420, h4422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h0, h2858, h4072, h4375, h4420, h4422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h0, h2858, h2859, h4373, h4375, hlam, p4423_2]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h0, h2858, h4373, h4375, h4420, h4422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4373, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4377, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            rcases p4423_3 (m.d 0 2) (by simp) with h4444 | h4444
                            · linarith only [h2859, h4444, hlam]
                            · linarith only [h4370, h4444, hlam]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h0, h2858, h4374, h4375, h4420, h4422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4374, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h0, h2858, h2859, h4374, h4375, h4420, h4422, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            rcases p4423_3 (m.d 0 2) (by simp) with h4451 | h4451
                            · linarith only [h4072, h4451, hlam]
                            · linarith only [h4370, h4451, hlam]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4370, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4375, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4420, hlam, p4423_1]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [h4421, hlam, p4423_0]
                          · have p4423_0 := h4423c.1
                            have p4423_1 := h4423c.2.1
                            have p4423_2 := h4423c.2.2.1
                            have p4423_3 := h4423c.2.2.2
                            linarith only [hlam, p4423_0]
                        · linarith only [h0, h2858, h4072, h4374, h4376, h4422, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h2858, h2859, h4376, h4377, h4421, hlam]
                    · linarith only [h2859, h4371, h4420, hlam]
                · linarith only [h0, h4072, h4372, h4374, h4376, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h0, h2858, h4072, h4374, h4375, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · linarith only [h0, h2858, h2859, h4373, h4374, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4465 | h4465
            · linarith only [h0, h2858, h4072, h4373, h4465, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4467 | h4467
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4468 | h4468
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4469 | h4469
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4470 | h4470
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4471 | h4471
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4472 | h4472
                        · rcases h2bigk with h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c | h4473c
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h0, hlam, p4473_1]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h2859, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4072, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            rcases p4473_3 (m.d 0 2) (by simp) with h4478 | h4478
                            · rcases p4473_3 (m.d 1 2) (by simp) with h4479 | h4479
                              · rcases p4473_3 (m.d 2 3) (by simp) with h4480 | h4480
                                · rcases p4473_3 (m.d 2 4) (by simp) with h4481 | h4481
                                  · rcases p4473_3 (m.d 2 5) (by simp) with h4482 | h4482
                                    · linarith only [h4482, hlam, p4473_0]
                                    · rcases h5bigk with h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c | h4484c
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h2858, h4467, h4470, h4472, hc45, hlam, hphi, ht0b, ht5b, p4484_1, u0elo0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h2858, h4465, h4470, h4472, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h2858, h4465, h4472, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h2858, h4465, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h2858, hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h2858, h4465, h4470, h4472, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h2858, h4465, h4469, h4472, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h2858, h4465, h4469, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4370, hlam, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4467, hlam, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4472, hc45, hlam, hphi, ht0b, ht5b, p4473_1, p4484_1, u0elo1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h4465, h4469, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4473_1, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4371, hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4371, hc15, hlam, hphi, ht0b, ht5b, p4484_1, u0elo2]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4470, hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h0, h4465, h4469, h4470, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4473_1, p4484_1]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4372, hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4468, hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4471, hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [h4472, hlam, p4484_0]
                                      · have p4484_0 := h4484c.1
                                        have p4484_1 := h4484c.2.1
                                        have p4484_2 := h4484c.2.2.1
                                        have p4484_3 := h4484c.2.2.2
                                        linarith only [hlam, p4484_0]
                                  · linarith only [h4471, h4481, hlam]
                                · linarith only [h4470, h4480, hlam]
                              · linarith only [h4467, h4479, hlam]
                            · linarith only [h4478, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4465, h4469, hc02, hc23, hlam, hphi, p4473_1]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4373, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4465, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            rcases p4473_3 (m.d 0 2) (by simp) with h4518 | h4518
                            · linarith only [h0, h4518, hlam]
                            · linarith only [h4370, h4518, hlam]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            rcases p4473_3 (m.d 0 2) (by simp) with h4521 | h4521
                            · linarith only [h4521, hlam, p4473_0]
                            · rcases p4473_3 (m.d 1 2) (by simp) with h4523 | h4523
                              · linarith only [h4373, h4523, hlam]
                              · linarith only [h0, h4523, hlam]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4473_1]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h0, h2858, h4072, h4467, h4470, h4472, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4473_1]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h0, h2858, h4373, h4467, hlam, p4473_2]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            rcases p4473_3 (m.d 0 2) (by simp) with h4530 | h4530
                            · linarith only [h4530, hlam, p4473_0]
                            · rcases p4473_3 (m.d 1 2) (by simp) with h4532 | h4532
                              · linarith only [h4465, h4532, hlam]
                              · linarith only [h0, h4532, hlam]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h0, h2858, h4467, h4469, h4470, h4472, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4473_1]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4469, hlam, p4473_1]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h0, h2858, h4465, h4467, hlam, p4473_2]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4370, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4467, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4470, hlam, p4473_1]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [h4471, hlam, p4473_0]
                          · have p4473_0 := h4473c.1
                            have p4473_1 := h4473c.2.1
                            have p4473_2 := h4473c.2.2.1
                            have p4473_3 := h4473c.2.2.2
                            linarith only [hlam, p4473_0]
                        · linarith only [h0, h2858, h4465, h4468, h4472, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h2858, h4465, h4468, h4471, hlam]
                    · linarith only [h0, h4465, h4469, h4470, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h4373, h4469, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h2858, h4372, h4465, h4468, hlam]
              · linarith only [h0, h4370, h4467, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h2858, h4072, h4372, hlam]
      · linarith only [h0, h2858, h2859, h4371, hlam]
    · linarith only [h0, h2858, h4370, hlam]

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h2859 | h2859
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0 m hb0 hb2 hb5 hg0 h2858 h2859
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x1 m hb0 hb2 hb5 hg0 h2858 h2859

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  exact r1l7_10_12_25_L_0_L_I_H_I_s2 m hb0 hb2 hb5 h0 h2858

set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h2858 | h2858
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x0 m hb0 hb2 hb5 hg0 h2858
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1_x1 m hb0 hb2 hb5 hg0 h2858

set_option maxHeartbeats 15398000 in
set_option maxHeartbeats 15398000 in
theorem r1l7_10_12_25_L_0_L_I_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_25_L_0_L_I_H_I_s0 m hb0 hb2 hb5 h0
  · exact r1l7_10_12_25_L_0_L_I_H_I_s1 m hb0 hb2 hb5 h0

end R2N4
