import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_21S18
import Jsp000404.R1LeavesN7_21S23

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5826000 in
set_option maxHeartbeats 5826000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3473 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3473 := hg3473
  rcases m.htr 0 1 4 (by decide) (by decide) with h4044 | h4044
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4045 | h4045
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4046 | h4046
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4047 | h4047
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4048 | h4048
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4049 | h4049
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4050 | h4050
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4051 | h4051
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4052 | h4052
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4053 | h4053
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4054 | h4054
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4055 | h4055
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4056 | h4056
                          · linarith only [h3473, h4044, h4056, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h3473, h4044, h4050, h4051, h4056, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h3473, h4045, h4055, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h3473, h4045, h4054, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h3473, h4044, h4050, h4051, h4053, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h3473, h4044, h4050, h4051, h4052, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h0, h4044, h4046, h4050, h4051, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4064 | h4064
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4065 | h4065
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4066 | h4066
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4067 | h4067
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4068 | h4068
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4069 | h4069
                          · linarith only [h3473, h4044, h4064, h4069, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4071 | h4071
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4072 | h4072
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4073 | h4073
                                · linarith only [h3473, h4045, h4050, h4064, h4065, h4069, h4073, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4075 | h4075
                                  · linarith only [h4044, h4050, h4065, h4071, h4075, hlam]
                                  · rcases h1bigk with h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c | h4077c
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h0, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h3473, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h3473, h4064, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4077_1, u4ehi1]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h3473, h4064, hc12, hlam, hphi, ht01, ht0b, ht5b, p4077_1, u5ehi1]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4044, h4065, h4071, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p4077_1, u4ehi3]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h3473, hc01, hc12, hlam, hphi, p4077_1]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      rcases p4077_3 (m.d 0 1) (by simp) with h4086 | h4086
                                      · linarith only [h0, h4086, hlam]
                                      · linarith only [h4044, h4086, hlam]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      rcases p4077_3 (m.d 0 1) (by simp) with h4089 | h4089
                                      · linarith only [h0, h4089, hlam]
                                      · linarith only [h4045, h4089, hlam]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4045, h4065, h4069, h4071, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p4077_1, u4ehi3]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4064, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      rcases p4077_3 (m.d 0 1) (by simp) with h4095 | h4095
                                      · linarith only [h3473, h4095, hlam]
                                      · linarith only [h4044, h4095, hlam]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      rcases p4077_3 (m.d 0 1) (by simp) with h4098 | h4098
                                      · linarith only [h3473, h4098, hlam]
                                      · linarith only [h4045, h4098, hlam]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4044, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4065, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4067, hlam, p4077_1]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4069, hlam, p4077_1]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4045, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4066, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4068, hlam, p4077_0]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [h4045, h4065, h4071, hc01, hlam, hphi, ht0b, ht45, ht5b, p4077_1, u4ehi3]
                                    · have p4077_0 := h4077c.1
                                      have p4077_1 := h4077c.2.1
                                      have p4077_2 := h4077c.2.2.1
                                      have p4077_3 := h4077c.2.2.2
                                      linarith only [hlam, p4077_0]
                              · linarith only [h3473, h4045, h4064, h4068, h4071, h4072, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4112 | h4112
                              · linarith only [h4064, h4067, h4071, h4112, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4114 | h4114
                                · linarith only [h4044, h4050, h4067, h4071, h4114, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4116 | h4116
                                  · linarith only [h4044, h4050, h4067, h4116, hlam]
                                  · rcases h1bigk with h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c | h4118c
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h0, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h3473, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h3473, h4064, h4067, h4071, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4118_1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h3473, h4064, hc12, hlam, hphi, ht01, ht0b, ht5b, p4118_1, u5ehi1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4044, h4067, h4071, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4118_1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h3473, hc01, hc12, hlam, hphi, p4118_1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      rcases p4118_3 (m.d 0 1) (by simp) with h4127 | h4127
                                      · linarith only [h0, h4127, hlam]
                                      · linarith only [h4044, h4127, hlam]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      rcases p4118_3 (m.d 0 1) (by simp) with h4130 | h4130
                                      · linarith only [h0, h4130, hlam]
                                      · linarith only [h4045, h4130, hlam]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4045, hc13, hlam, hphi, ht01, ht0b, ht5b, p4118_1, u5ehi1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4064, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      rcases p4118_3 (m.d 0 1) (by simp) with h4136 | h4136
                                      · linarith only [h3473, h4136, hlam]
                                      · linarith only [h4044, h4136, hlam]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      rcases p4118_3 (m.d 0 1) (by simp) with h4139 | h4139
                                      · linarith only [h3473, h4139, hlam]
                                      · linarith only [h4045, h4139, hlam]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4044, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4065, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4067, hlam, p4118_1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4069, hlam, p4118_1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4045, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4066, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4068, hlam, p4118_0]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [h4045, h4067, h4071, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4118_1]
                                    · have p4118_0 := h4118c.1
                                      have p4118_1 := h4118c.2.1
                                      have p4118_2 := h4118c.2.2.1
                                      have p4118_3 := h4118c.2.2.2
                                      linarith only [hlam, p4118_0]
                        · linarith only [h3473, h4044, h4068, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                      · linarith only [h3473, h4044, h4065, h4067, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h4044, h4065, h4066, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h3473, h4044, h4064, h4065, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h4044, h4064, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h3473, h4045, h4049, hlam]
          · linarith only [h0, h4045, h4048, hlam]
        · linarith only [h3473, h4044, h4046, h4047, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4160 | h4160
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4161 | h4161
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4162 | h4162
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4163 | h4163
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4164 | h4164
                · linarith only [h4046, h4160, h4164, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h4044, h4163, h4164, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4167 | h4167
                · linarith only [h0, h4045, h4046, h4167, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h4044, h4167, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h4045, h4046, h4162, hlam]
          · linarith only [h0, h4045, h4161, hlam]
        · linarith only [h0, h4044, h4160, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4173 | h4173
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4174 | h4174
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4175 | h4175
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4176 | h4176
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4177 | h4177
              · linarith only [h4044, h4045, h4177, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4179 | h4179
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4180 | h4180
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4181 | h4181
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4182 | h4182
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4183 | h4183
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4184 | h4184
                          · linarith only [h4044, h4177, h4184, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h4044, h4045, h4180, h4184, hc45, hlam, hphi, u4ehi2]
                        · linarith only [h3473, h4044, h4173, h4176, h4180, h4183, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h3473, h4044, h4180, h4182, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h4044, h4180, h4181, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h3473, h4044, h4179, h4180, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h4173, h4179, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4192 | h4192
              · linarith only [h4044, h4045, h4192, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4194 | h4194
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4195 | h4195
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4196 | h4196
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4197 | h4197
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4198 | h4198
                        · linarith only [h3473, h4044, h4176, h4195, h4198, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h3473, h4044, h4195, h4198, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h3473, h4044, h4195, h4197, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h4044, h4195, h4196, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h3473, h4044, h4194, h4195, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h4044, h4173, h4194, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4205 | h4205
            · linarith only [h4173, h4175, h4205, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4207 | h4207
              · linarith only [h0, h4044, h4175, h4207, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4209 | h4209
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4210 | h4210
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4211 | h4211
                    · linarith only [h3473, h4044, h4173, h4175, h4210, h4211, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h4044, h4210, h4211, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h3473, h4044, h4209, h4210, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h4044, h4173, h4209, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
        · linarith only [h0, h4044, h4174, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4217 | h4217
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4218 | h4218
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4219 | h4219
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4220 | h4220
              · linarith only [h4044, h4045, h4220, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4222 | h4222
                · linarith only [h4173, h4217, h4222, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h4044, h4222, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h4173, h4218, h4219, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4226 | h4226
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4227 | h4227
              · linarith only [h0, h4044, h4218, h4227, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4229 | h4229
                · linarith only [h4173, h4217, h4229, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h4044, h4229, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4232 | h4232
              · linarith only [h3473, h4044, h4226, h4232, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4234 | h4234
                · linarith only [h0, h4044, h4173, h4234, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h4044, h4234, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h0, h4044, h4217, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s6 m hb1 hb2 hb4 hb5 h0 h3473 h4044

set_option maxHeartbeats 6968000 in
set_option maxHeartbeats 6968000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h3473 | h3473
  · rcases m.htr 0 1 4 (by decide) (by decide) with h3474 | h3474
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3475 | h3475
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3476 | h3476
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3477 | h3477
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3478 | h3478
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3479 | h3479
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3480 | h3480
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3481 | h3481
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3482 | h3482
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3483 | h3483
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3484 | h3484
                        · linarith only [h0, h3473, h3484, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3486 | h3486
                          · linarith only [h0, h3474, h3484, h3486, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3488 | h3488
                            · linarith only [h0, h3474, h3488, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h3474, h3480, h3488, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h3473, h3479, h3483, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h3473, h3479, h3482, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3474, h3480, h3481, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3494 | h3494
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3495 | h3495
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3496 | h3496
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3497 | h3497
                        · linarith only [h0, h3473, h3497, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3499 | h3499
                          · linarith only [h0, h3474, h3497, h3499, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3501 | h3501
                            · linarith only [h0, h3474, h3480, h3501, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3503 | h3503
                              · linarith only [h0, h3473, h3494, h3497, h3503, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3505 | h3505
                                · linarith only [h3494, h3499, h3505, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3507 | h3507
                                  · linarith only [h3477, h3480, h3507, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3509 | h3509
                                    · linarith only [h0, h3473, h3474, h3479, h3480, h3495, h3509, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                    · rcases h1bigk with h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c | h3511c
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h0, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        rcases p3511_3 (m.d 0 1) (by simp) with h3514 | h3514
                                        · rcases p3511_3 (m.d 1 2) (by simp) with h3515 | h3515
                                          · rcases p3511_3 (m.d 1 3) (by simp) with h3516 | h3516
                                            · linarith only [h3516, hlam, p3511_0]
                                            · rcases p3511_3 (m.d 1 4) (by simp) with h3518 | h3518
                                              · linarith only [h3474, h3518, hlam]
                                              · linarith only [h3497, h3518, hlam]
                                          · linarith only [h3494, h3515, hlam]
                                        · linarith only [h3514, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h0, h3495, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3511_1, u4ehi2]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3511_1, u5ehi1]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3473, h3479, hc12, hlam, hphi, ht01, ht0b, ht5b, p3511_1, u5ehi3]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h0, h3473, h3479, h3499, hlam, p3511_2]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        rcases p3511_3 (m.d 0 1) (by simp) with h3528 | h3528
                                        · linarith only [h0, h3528, hlam]
                                        · linarith only [h3474, h3528, hlam]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        rcases p3511_3 (m.d 0 1) (by simp) with h3531 | h3531
                                        · linarith only [h0, h3531, hlam]
                                        · linarith only [h3475, h3531, hlam]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3473, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3494, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3497, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3499, hlam, p3511_1]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3474, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3495, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h0, h3474, h3494, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3511_1]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3501, hlam, p3511_1]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3475, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h3496, hlam, p3511_0]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h0, h3473, h3479, h3494, h3499, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3511_1]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [h0, h3473, h3479, h3499, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3511_1, u4ehi1]
                                      · have p3511_0 := h3511c.1
                                        have p3511_1 := h3511c.2.1
                                        have p3511_2 := h3511c.2.2.1
                                        have p3511_3 := h3511c.2.2.2
                                        linarith only [hlam, p3511_0]
                      · linarith only [h0, h3473, h3479, h3496, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h3473, h3479, h3495, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3473, h3479, h3494, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3552 | h3552
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3553 | h3553
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3554 | h3554
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3555 | h3555
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3556 | h3556
                        · linarith only [h0, h3473, h3556, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3558 | h3558
                          · linarith only [h0, h3474, h3479, h3556, h3558, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3560 | h3560
                            · linarith only [h0, h3474, h3560, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h3474, h3552, h3560, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h3474, h3552, h3555, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h3474, h3552, h3554, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h3474, h3552, h3553, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3566 | h3566
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3567 | h3567
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3568 | h3568
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3569 | h3569
                        · linarith only [h0, h3473, h3569, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3571 | h3571
                          · linarith only [h3473, h3479, h3571, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3573 | h3573
                            · linarith only [h0, h3474, h3552, h3573, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3575 | h3575
                              · linarith only [h3566, h3569, h3575, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3577 | h3577
                                · linarith only [h3473, h3479, h3566, h3577, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3579 | h3579
                                  · linarith only [h3474, h3552, h3567, h3579, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3581 | h3581
                                    · rcases h1bigk with h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c | h3582c
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h0, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        rcases p3582_3 (m.d 0 1) (by simp) with h3585 | h3585
                                        · rcases p3582_3 (m.d 1 2) (by simp) with h3586 | h3586
                                          · rcases p3582_3 (m.d 1 3) (by simp) with h3587 | h3587
                                            · linarith only [h3587, hlam, p3582_0]
                                            · rcases p3582_3 (m.d 1 4) (by simp) with h3589 | h3589
                                              · linarith only [h3474, h3589, hlam]
                                              · linarith only [h3569, h3589, hlam]
                                          · linarith only [h3566, h3586, hlam]
                                        · linarith only [h3585, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3582_1, u4ehi1]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h0, h3567, h3573, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3582_1, u4ehi2]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3474, h3567, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3582_1, u4ehi2]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        rcases p3582_3 (m.d 0 1) (by simp) with h3598 | h3598
                                        · linarith only [h0, h3598, hlam]
                                        · linarith only [h3473, h3598, hlam]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        rcases p3582_3 (m.d 0 1) (by simp) with h3601 | h3601
                                        · linarith only [h0, h3601, hlam]
                                        · linarith only [h3474, h3601, hlam]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        rcases p3582_3 (m.d 0 1) (by simp) with h3604 | h3604
                                        · linarith only [h0, h3604, hlam]
                                        · linarith only [h3475, h3604, hlam]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3473, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3566, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3569, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3571, hlam, p3582_1]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3474, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3567, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3474, h3552, h3581, hc13, hc34, hlam, hphi, p3582_1]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3573, hlam, p3582_1]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3475, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h3568, hlam, p3582_0]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h0, h3474, h3475, h3552, h3566, h3567, h3581, hc12, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3582_1, u4ehi2]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [h0, h3475, h3567, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3582_1, u4ehi2]
                                      · have p3582_0 := h3582c.1
                                        have p3582_1 := h3582c.2.1
                                        have p3582_2 := h3582c.2.2.1
                                        have p3582_3 := h3582c.2.2.2
                                        linarith only [hlam, p3582_0]
                                    · rcases h1bigk with h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c | h3622c
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h0, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        rcases p3622_3 (m.d 0 1) (by simp) with h3625 | h3625
                                        · rcases p3622_3 (m.d 1 2) (by simp) with h3626 | h3626
                                          · rcases p3622_3 (m.d 1 3) (by simp) with h3627 | h3627
                                            · linarith only [h3627, hlam, p3622_0]
                                            · rcases p3622_3 (m.d 1 4) (by simp) with h3629 | h3629
                                              · linarith only [h3474, h3629, hlam]
                                              · linarith only [h3569, h3629, hlam]
                                          · linarith only [h3566, h3626, hlam]
                                        · linarith only [h3625, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h0, h3567, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3622_1, u4ehi2]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p3622_1, u5ehi1]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3474, h3567, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3622_1, u4ehi2]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        rcases p3622_3 (m.d 0 1) (by simp) with h3638 | h3638
                                        · linarith only [h0, h3638, hlam]
                                        · linarith only [h3473, h3638, hlam]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        rcases p3622_3 (m.d 0 1) (by simp) with h3641 | h3641
                                        · linarith only [h0, h3641, hlam]
                                        · linarith only [h3474, h3641, hlam]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        rcases p3622_3 (m.d 0 1) (by simp) with h3644 | h3644
                                        · linarith only [h0, h3644, hlam]
                                        · linarith only [h3475, h3644, hlam]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3473, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3566, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3569, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3571, hlam, p3622_1]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3474, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3567, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h0, h3475, h3566, h3573, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3622_1]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3573, hlam, p3622_1]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3475, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h3568, hlam, p3622_0]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h0, h3475, h3566, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3622_1]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [h0, h3475, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3622_1, u4ehi1]
                                      · have p3622_0 := h3622c.1
                                        have p3622_1 := h3622c.2.1
                                        have p3622_2 := h3622c.2.2.1
                                        have p3622_3 := h3622c.2.2.2
                                        linarith only [hlam, p3622_0]
                      · linarith only [h0, h3474, h3567, h3568, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h3474, h3567, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h3474, h3566, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h3475, h3478, hlam]
          · linarith only [h0, h3474, h3477, hlam]
        · linarith only [h0, h3473, h3476, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3668 | h3668
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3669 | h3669
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3670 | h3670
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3671 | h3671
              · linarith only [h3473, h3475, h3671, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3673 | h3673
                · linarith only [h3474, h3475, h3673, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3675 | h3675
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3676 | h3676
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3677 | h3677
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3678 | h3678
                        · linarith only [h3473, h3475, h3677, h3678, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3680 | h3680
                          · linarith only [h3474, h3475, h3671, h3677, h3678, h3680, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3682 | h3682
                            · linarith only [h3474, h3475, h3673, h3680, h3682, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                            · linarith only [h3474, h3475, h3682, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h0, h3474, h3670, h3676, h3677, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h3474, h3676, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h3474, h3675, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3688 | h3688
              · linarith only [h0, h3473, h3670, h3688, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3690 | h3690
                · linarith only [h0, h3474, h3670, h3690, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3692 | h3692
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3693 | h3693
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3694 | h3694
                      · linarith only [h0, h3474, h3670, h3693, h3694, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h3474, h3693, h3694, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h3474, h3693, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h3474, h3668, h3692, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h0, h3474, h3669, hlam]
        · linarith only [h0, h3473, h3668, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3701 | h3701
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3702 | h3702
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3703 | h3703
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3704 | h3704
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3705 | h3705
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3706 | h3706
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3707 | h3707
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3708 | h3708
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3709 | h3709
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3710 | h3710
                        · linarith only [h3473, h3474, h3710, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3712 | h3712
                          · linarith only [h3473, h3474, h3710, h3712, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h3473, h3474, h3705, h3710, h3712, hc13, hc34, hlam, hphi]
                      · linarith only [h3474, h3701, h3708, h3709, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h3703, h3708, hlam]
                  · linarith only [h0, h3701, h3707, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h3473, h3474, h3705, h3706, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3719 | h3719
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3720 | h3720
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3721 | h3721
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3722 | h3722
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3723 | h3723
                        · linarith only [h3473, h3474, h3721, h3723, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3725 | h3725
                          · linarith only [h3473, h3474, h3705, h3723, h3725, hc03, hc34, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3727 | h3727
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3728 | h3728
                              · linarith only [h3474, h3701, h3720, h3723, h3725, h3728, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3730 | h3730
                                · linarith only [h3473, h3705, h3720, h3730, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3732 | h3732
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3733 | h3733
                                    · rcases h1bigk with h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c | h3734c
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h0, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3474, h3723, hc13, hc34, hlam, hphi, p3734_1]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3474, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3474, h3723, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3734_1, u5ehi1]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3701, h3722, h3732, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3734_1, u4ehi4]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        rcases p3734_3 (m.d 0 1) (by simp) with h3742 | h3742
                                        · linarith only [h0, h3742, hlam]
                                        · linarith only [h3473, h3742, hlam]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3474, h3701, h3722, h3732, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3734_1, u4ehi4]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        rcases p3734_3 (m.d 0 1) (by simp) with h3746 | h3746
                                        · linarith only [h0, h3746, hlam]
                                        · linarith only [h3701, h3746, hlam]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3473, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3720, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3723, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3725, hlam, p3734_1]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3701, h3722, h3732, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p3734_1, u4ehi4]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3721, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        rcases p3734_3 (m.d 0 1) (by simp) with h3756 | h3756
                                        · linarith only [h3474, h3756, hlam]
                                        · linarith only [h3473, h3756, hlam]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        rcases p3734_3 (m.d 0 1) (by simp) with h3760 | h3760
                                        · linarith only [h3474, h3760, hlam]
                                        · linarith only [h3701, h3760, hlam]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3701, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3722, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h0, h3701, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3734_1]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [h3727, hlam, p3734_0]
                                      · have p3734_0 := h3734c.1
                                        have p3734_1 := h3734c.2.1
                                        have p3734_2 := h3734c.2.2.1
                                        have p3734_3 := h3734c.2.2.2
                                        linarith only [hlam, p3734_0]
                                    · linarith only [h3474, h3701, h3722, h3723, h3732, h3733, hlam]
                                  · linarith only [h3474, h3701, h3723, h3727, h3732, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                            · linarith only [h3474, h3701, h3719, h3727, hc04, hlam, hphi, ht0b, ht5b, u5ehi0]
                      · linarith only [h0, h3701, h3722, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h3701, h3721, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h3701, h3720, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h3474, h3701, h3719, hlam]
            · linarith only [h0, h3701, h3704, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3776 | h3776
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3777 | h3777
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3778 | h3778
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3779 | h3779
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3780 | h3780
                    · linarith only [h3703, h3776, h3780, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h3473, h3777, h3780, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3473, h3777, h3779, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h3701, h3703, h3778, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3785 | h3785
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3786 | h3786
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3787 | h3787
                    · linarith only [h0, h3701, h3703, h3787, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                    · linarith only [h0, h3701, h3787, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h3701, h3786, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h3701, h3703, h3785, hlam]
            · linarith only [h0, h3701, h3776, hlam]
        · linarith only [h0, h3473, h3702, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3794 | h3794
        · rcases m.htr 0 2 4 (by decide) (by decide) with h3795 | h3795
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3796 | h3796
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3797 | h3797
              · linarith only [h3473, h3701, h3797, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3799 | h3799
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3800 | h3800
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3801 | h3801
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3802 | h3802
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3803 | h3803
                        · linarith only [h3473, h3474, h3801, h3803, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3805 | h3805
                          · linarith only [h3473, h3701, h3797, h3805, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3807 | h3807
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3808 | h3808
                              · linarith only [h3473, h3701, h3794, h3803, h3807, h3808, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3810 | h3810
                                · linarith only [h3473, h3701, h3800, h3805, h3810, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3812 | h3812
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3813 | h3813
                                    · rcases h1bigk with h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c | h3814c
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h0, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3701, h3800, h3803, h3807, hc23, hc34, hlam, hphi, p3814_1]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3474, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3701, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        rcases p3814_3 (m.d 0 1) (by simp) with h3820 | h3820
                                        · linarith only [h3820, hlam, p3814_0]
                                        · rcases p3814_3 (m.d 1 2) (by simp) with h3822 | h3822
                                          · rcases p3814_3 (m.d 1 3) (by simp) with h3823 | h3823
                                            · linarith only [h3800, h3823, hlam]
                                            · rcases p3814_3 (m.d 1 4) (by simp) with h3825 | h3825
                                              · linarith only [h3801, h3825, hlam]
                                              · linarith only [h3474, h3825, hlam]
                                          · linarith only [h3822, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        rcases p3814_3 (m.d 0 1) (by simp) with h3830 | h3830
                                        · linarith only [h0, h3830, hlam]
                                        · linarith only [h3473, h3830, hlam]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3474, hc01, hc12, hlam, hphi, p3814_1]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3473, h3701, h3800, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3814_1]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3473, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3800, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3803, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3805, hlam, p3814_1]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3473, h3800, h3803, hc23, hc34, hlam, hphi, p3814_1]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3801, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        rcases p3814_3 (m.d 0 1) (by simp) with h3842 | h3842
                                        · linarith only [h3474, h3842, hlam]
                                        · linarith only [h3473, h3842, hlam]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3473, h3701, h3800, h3803, hc23, hc34, hlam, hphi, p3814_1]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3473, h3800, h3805, hc23, hc35, hlam, hphi, p3814_1]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3802, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        rcases p3814_3 (m.d 0 1) (by simp) with h3849 | h3849
                                        · linarith only [h3701, h3849, hlam]
                                        · linarith only [h3473, h3849, hlam]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [h3807, hlam, p3814_0]
                                      · have p3814_0 := h3814c.1
                                        have p3814_1 := h3814c.2.1
                                        have p3814_2 := h3814c.2.2.1
                                        have p3814_3 := h3814c.2.2.2
                                        linarith only [hlam, p3814_0]
                                    · linarith only [h3473, h3474, h3795, h3800, h3803, h3812, h3813, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3855 | h3855
                                    · rcases h1bigk with h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c | h3856c
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h0, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3474, h3800, h3803, hc23, hc34, hlam, hphi, p3856_1]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3474, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3701, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        rcases p3856_3 (m.d 0 1) (by simp) with h3862 | h3862
                                        · linarith only [h3862, hlam, p3856_0]
                                        · rcases p3856_3 (m.d 1 2) (by simp) with h3864 | h3864
                                          · rcases p3856_3 (m.d 1 3) (by simp) with h3865 | h3865
                                            · linarith only [h3800, h3865, hlam]
                                            · rcases p3856_3 (m.d 1 4) (by simp) with h3867 | h3867
                                              · linarith only [h3801, h3867, hlam]
                                              · linarith only [h3474, h3867, hlam]
                                          · linarith only [h3864, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        rcases p3856_3 (m.d 0 1) (by simp) with h3872 | h3872
                                        · linarith only [h0, h3872, hlam]
                                        · linarith only [h3473, h3872, hlam]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3474, h3799, h3812, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p3856_1, u4ehi2]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3701, hc01, hc12, hlam, hphi, p3856_1]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3473, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3800, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3803, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3805, hlam, p3856_1]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3473, h3803, hc13, hc34, hlam, hphi, p3856_1]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3801, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        rcases p3856_3 (m.d 0 1) (by simp) with h3884 | h3884
                                        · linarith only [h3474, h3884, hlam]
                                        · linarith only [h3473, h3884, hlam]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3473, h3701, h3800, h3803, hc23, hc34, hlam, hphi, p3856_1]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3473, h3800, h3805, hc23, hc35, hlam, hphi, p3856_1]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3802, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        rcases p3856_3 (m.d 0 1) (by simp) with h3891 | h3891
                                        · linarith only [h3701, h3891, hlam]
                                        · linarith only [h3473, h3891, hlam]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [h3807, hlam, p3856_0]
                                      · have p3856_0 := h3856c.1
                                        have p3856_1 := h3856c.2.1
                                        have p3856_2 := h3856c.2.2.1
                                        have p3856_3 := h3856c.2.2.2
                                        linarith only [hlam, p3856_0]
                                    · linarith only [h3474, h3799, h3803, h3855, hlam]
                            · linarith only [h3474, h3799, h3807, hlam]
                      · linarith only [h0, h3796, h3802, hlam]
                    · linarith only [h0, h3795, h3801, hlam]
                  · linarith only [h0, h3794, h3800, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3901 | h3901
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3902 | h3902
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3903 | h3903
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3904 | h3904
                        · linarith only [h3473, h3474, h3902, h3904, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3906 | h3906
                          · linarith only [h3473, h3474, h3797, h3799, h3906, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3908 | h3908
                            · linarith only [h3473, h3474, h3799, h3904, h3908, hc13, hc34, hlam, hphi]
                            · linarith only [h3473, h3474, h3901, h3908, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h3473, h3474, h3796, h3901, h3902, h3903, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h3795, h3902, hlam]
                  · linarith only [h0, h3794, h3901, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3914 | h3914
              · linarith only [h0, h3473, h3796, h3914, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3916 | h3916
                · linarith only [h3795, h3796, h3916, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3918 | h3918
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3919 | h3919
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3920 | h3920
                      · linarith only [h3795, h3796, h3920, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3922 | h3922
                        · linarith only [h3473, h3474, h3919, h3920, h3922, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3924 | h3924
                          · linarith only [h3473, h3474, h3914, h3919, h3920, h3924, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3926 | h3926
                            · linarith only [h3916, h3919, h3920, h3926, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                            · linarith only [h3473, h3474, h3926, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h3795, h3796, h3919, hc12, hc25, hlam, hphi]
                  · linarith only [h0, h3794, h3918, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h3931 | h3931
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3932 | h3932
              · linarith only [h3473, h3701, h3932, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3934 | h3934
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3935 | h3935
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3936 | h3936
                    · linarith only [h3795, h3931, h3936, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3938 | h3938
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3939 | h3939
                        · linarith only [h3473, h3701, h3939, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3941 | h3941
                          · linarith only [h3473, h3701, h3932, h3936, h3938, h3941, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3943 | h3943
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3944 | h3944
                              · linarith only [h3473, h3701, h3935, h3936, h3938, h3939, h3944, hlam]
                              · linarith only [h3473, h3701, h3936, h3938, h3944, hc13, hc34, hlam, hphi]
                            · linarith only [h3473, h3701, h3934, h3935, h3936, h3938, h3943, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3473, h3931, h3935, h3938, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3794, h3935, hlam]
                · linarith only [h3795, h3931, h3934, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3951 | h3951
              · linarith only [h3473, h3701, h3951, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3953 | h3953
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3954 | h3954
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3955 | h3955
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3956 | h3956
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3957 | h3957
                        · linarith only [h0, h3473, h3795, h3955, h3957, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3959 | h3959
                          · linarith only [h0, h3473, h3795, h3951, h3955, h3959, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3961 | h3961
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3962 | h3962
                              · linarith only [h0, h3473, h3795, h3954, h3955, h3957, h3962, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3964 | h3964
                                · linarith only [h0, h3473, h3795, h3954, h3955, h3964, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h3966 | h3966
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3967 | h3967
                                    · rcases h1bigk with h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c | h3968c
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h0, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h0, h3931, h3955, h3966, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3968_1]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3474, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3701, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        rcases p3968_3 (m.d 0 1) (by simp) with h3974 | h3974
                                        · linarith only [h3974, hlam, p3968_0]
                                        · rcases p3968_3 (m.d 1 2) (by simp) with h3976 | h3976
                                          · rcases p3968_3 (m.d 1 3) (by simp) with h3977 | h3977
                                            · linarith only [h3954, h3977, hlam]
                                            · rcases p3968_3 (m.d 1 4) (by simp) with h3979 | h3979
                                              · linarith only [h3955, h3979, hlam]
                                              · linarith only [h3474, h3979, hlam]
                                          · linarith only [h3976, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h0, h3473, h3931, h3955, h3966, hlam, p3968_2]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h0, h3931, h3956, h3961, hc01, hc12, hlam, hphi, p3968_1]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h0, h3473, h3931, h3954, h3956, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3968_1]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3473, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3954, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3957, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3959, hlam, p3968_1]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3473, h3954, h3957, hc23, hc34, hlam, hphi, p3968_1]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3955, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        rcases p3968_3 (m.d 0 1) (by simp) with h3994 | h3994
                                        · linarith only [h3474, h3994, hlam]
                                        · linarith only [h3473, h3994, hlam]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h0, h3473, h3931, h3954, h3956, h3957, hc23, hc34, hlam, hphi, p3968_1]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3473, h3954, h3959, hc23, hc35, hlam, hphi, p3968_1]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3956, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        rcases p3968_3 (m.d 0 1) (by simp) with h4001 | h4001
                                        · linarith only [h3701, h4001, hlam]
                                        · linarith only [h3473, h4001, hlam]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [h3961, hlam, p3968_0]
                                      · have p3968_0 := h3968c.1
                                        have p3968_1 := h3968c.2.1
                                        have p3968_2 := h3968c.2.2.1
                                        have p3968_3 := h3968c.2.2.2
                                        linarith only [hlam, p3968_0]
                                    · linarith only [h3473, h3474, h3953, h3954, h3957, h3967, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h3795, h3953, h3966, hlam]
                            · linarith only [h3473, h3474, h3953, h3954, h3961, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3473, h3795, h3954, h3955, h3956, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4010 | h4010
                      · linarith only [h0, h3473, h3931, h3954, h3955, h4010, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4012 | h4012
                        · linarith only [h0, h3473, h3955, h4012, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4014 | h4014
                          · linarith only [h0, h3473, h3955, h4014, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4016 | h4016
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4017 | h4017
                              · linarith only [h0, h3473, h3474, h3954, h3955, h4012, h4017, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                              · linarith only [h0, h3473, h3954, h3955, h4017, hc23, hc34, hlam, hphi]
                            · linarith only [h3473, h3474, h3954, h4016, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h3473, h3794, h3931, h3953, h3954, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4022 | h4022
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4023 | h4023
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4024 | h4024
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4025 | h4025
                        · linarith only [h0, h3473, h3931, h4024, h4025, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4027 | h4027
                          · linarith only [h0, h3473, h3795, h3951, h4023, h4027, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4029 | h4029
                            · linarith only [h3473, h3474, h3953, h4025, h4029, hc13, hc34, hlam, hphi]
                            · linarith only [h3473, h3474, h4022, h4029, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h3473, h3795, h4022, h4023, h4024, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4033 | h4033
                      · linarith only [h0, h3473, h3931, h4022, h4023, h4033, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4035 | h4035
                        · linarith only [h0, h3473, h4023, h4035, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4037 | h4037
                          · linarith only [h0, h3473, h4023, h4037, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4039 | h4039
                            · linarith only [h0, h3473, h3795, h3953, h4035, h4039, hc13, hc34, hlam, hphi]
                            · linarith only [h3473, h3474, h4022, h4039, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h3473, h3794, h4022, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h3473, h3794, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s5 m hb1 hb2 hb4 hb5 h0 h3473

set_option maxHeartbeats 13914000 in
set_option maxHeartbeats 13914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_M_IR_s4 m hb1 hb2 hb4 hb5 h0

end R2N4
