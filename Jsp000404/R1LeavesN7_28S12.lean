import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_28S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3210 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3211 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 5 (by decide) (by decide) with h4010 | h4010
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4011 | h4011
    · linarith only [h3210, h3211, h4011, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4013 | h4013
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4014 | h4014
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4015 | h4015
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4016 | h4016
            · linarith only [h3210, h3211, h4013, h4016, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4018 | h4018
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4019 | h4019
                · linarith only [h4011, h4013, h4019, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4021 | h4021
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4022 | h4022
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4023 | h4023
                      · linarith only [h3210, h4019, h4023, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4025 | h4025
                        · linarith only [h0, h3210, h4016, h4023, h4025, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h0, h3210, h4013, h4016, h4023, h4025, hc23, hc34, hlam, hphi]
                    · linarith only [h2722, h4014, h4022, hlam]
                  · linarith only [h1833, h4013, h4021, hlam]
              · linarith only [h0, h4010, h4018, hlam]
          · linarith only [h0, h3210, h4015, hlam]
        · linarith only [h3211, h4010, h4014, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4033 | h4033
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4034 | h4034
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4035 | h4035
            · linarith only [h3211, h4010, h4035, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4037 | h4037
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4038 | h4038
                · linarith only [h1833, h4011, h4034, h4035, h4038, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4040 | h4040
                  · linarith only [h1833, h4013, h4034, h4035, h4040, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4042 | h4042
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4043 | h4043
                      · linarith only [h1833, h3210, h4038, h4043, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4045 | h4045
                        · linarith only [h0, h1833, h3210, h4035, h4040, h4043, h4045, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4047 | h4047
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4048 | h4048
                            · rcases h0bigk with h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c | h4049c
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [hlam, p4049_0]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h0, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h1833, hlam, p4049_0]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h2722, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h3122, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h0, h4035, h4043, hc01, hc34, hlam, hphi, ht12, ht23, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [hlam, p4049_0]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h0, h4035, h4043, hc03, hc34, hlam, hphi, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h3211, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h0, h4035, h4043, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4049_1, u5ehi0]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h1833, h4040, hc01, hc35, hlam, hphi, ht12, ht23, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h3210, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [hlam, p4049_0]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h4011, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h4013, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                rcases p4049_3 (m.d 0 1) (by simp) with h4065 | h4065
                                · linarith only [h2722, h4065, hlam]
                                · rcases p4049_3 (m.d 0 2) (by simp) with h4067 | h4067
                                  · linarith only [h3211, h4067, hlam]
                                  · linarith only [h0, h4067, hlam]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h4010, h4045, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4049_1, u0elo3]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                rcases p4049_3 (m.d 0 1) (by simp) with h4071 | h4071
                                · linarith only [h2722, h4071, hlam]
                                · rcases p4049_3 (m.d 0 2) (by simp) with h4073 | h4073
                                  · linarith only [h3211, h4073, hlam]
                                  · linarith only [h3210, h4073, hlam]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [hlam, p4049_0]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h4010, h4047, hlam, hphi, ht0b, ht5b, p4049_1, u0elo3, u5ehi4]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h0, h4010, h4035, h4043, hc01, hc34, hlam, hphi, ht12, ht23, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h4010, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h0, h1833, h4010, h4035, h4043, hc01, hc34, hlam, hphi, ht12, ht23, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [h4033, hlam, p4049_1]
                              · have p4049_0 := h4049c.1
                                have p4049_1 := h4049c.2.1
                                have p4049_2 := h4049c.2.2.1
                                have p4049_3 := h4049c.2.2.2
                                linarith only [hlam, p4049_0]
                            · linarith only [h0, h4010, h4035, h4043, h4047, h4048, hlam]
                          · linarith only [h0, h4010, h4035, h4047, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · linarith only [h2722, h4033, h4042, hlam]
              · linarith only [h0, h4010, h4037, hlam]
          · linarith only [h0, h3210, h4034, hlam]
        · linarith only [h3211, h4010, h4033, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4089 | h4089
    · linarith only [h3210, h3211, h4089, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4091 | h4091
      · linarith only [h3210, h4010, h4091, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4093 | h4093
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4094 | h4094
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4095 | h4095
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4096 | h4096
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4097 | h4097
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4098 | h4098
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4099 | h4099
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4100 | h4100
                      · linarith only [h3210, h3211, h4089, h4095, h4100, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4102 | h4102
                        · linarith only [h1833, h3210, h3211, h4091, h4094, h4097, h4100, h4102, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4104 | h4104
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4105 | h4105
                            · rcases h0bigk with h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c | h4106c
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [hlam, p4106_0]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h0, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h1833, hlam, p4106_0]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h2722, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3122, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h4010, h4094, h4097, h4100, h4104, hc01, hc12, hlam, hphi, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [hlam, p4106_0]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h1833, h4010, h4094, h4097, h4100, h4104, hc01, hc12, hlam, hphi, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3211, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h4010, hlam, p4106_0]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3210, h4010, h4094, h4097, h4100, h4104, hc01, hc12, hlam, hphi, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3210, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [hlam, p4106_0]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h4089, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h4091, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3211, h4094, h4097, h4100, hc01, hc12, hlam, hphi, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3210, h3211, h4094, h4097, h4100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h1833, h3211, h4094, h4097, h4100, hc01, hc12, hlam, hphi, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [hlam, p4106_0]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3210, h3211, h4010, h4094, h4097, h4100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h4010, h4094, h4097, h4100, h4104, hc01, hc12, hlam, hphi, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h3210, h4010, h4094, h4097, h4100, h4104, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h1833, h4010, h4094, h4097, h4100, h4104, hc01, hc12, hlam, hphi, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [h4093, hlam, p4106_1]
                              · have p4106_0 := h4106c.1
                                have p4106_1 := h4106c.2.1
                                have p4106_2 := h4106c.2.2.1
                                have p4106_3 := h4106c.2.2.2
                                linarith only [hlam, p4106_0]
                            · linarith only [h3210, h3211, h4100, h4105, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h3211, h4093, h4104, hlam]
                    · linarith only [h2722, h4093, h4099, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1833, h4089, h4097, h4098, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4136 | h4136
                  · linarith only [h1833, h4091, h4097, h4136, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4138 | h4138
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4139 | h4139
                      · linarith only [h3210, h4097, h4139, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4141 | h4141
                        · linarith only [h1833, h3210, h4136, h4141, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4143 | h4143
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4144 | h4144
                            · rcases h0bigk with h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c | h4145c
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
                                linarith only [h1833, hlam, p4145_0]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h2722, hlam, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3122, hlam, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h4010, h4095, h4143, hc01, hc12, hlam, hphi, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [hlam, p4145_0]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h1833, h4010, h4095, h4143, hc01, hc12, hlam, hphi, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3211, hlam, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h4010, hlam, p4145_0]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3210, h4010, h4095, h4143, hc01, hc12, hlam, hphi, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3210, hlam, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [hlam, p4145_0]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h4089, hlam, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h4091, hlam, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3211, h4095, hc01, hc12, hlam, hphi, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3210, h3211, h4095, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h1833, h3211, h4095, hc01, hc12, hlam, hphi, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [hlam, p4145_0]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3210, h3211, h4010, h4095, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h4010, h4095, h4143, hc01, hc12, hlam, hphi, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h3210, h4010, h4095, h4143, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h1833, h4010, h4095, h4143, hc01, hc12, hlam, hphi, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [h4093, hlam, p4145_1]
                              · have p4145_0 := h4145c.1
                                have p4145_1 := h4145c.2.1
                                have p4145_2 := h4145c.2.2.1
                                have p4145_3 := h4145c.2.2.2
                                linarith only [hlam, p4145_0]
                            · linarith only [h2722, h4093, h4097, h4144, hlam]
                          · linarith only [h3210, h3211, h4143, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h2722, h4093, h4138, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · linarith only [h3211, h4093, h4095, h4096, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4175 | h4175
              · linarith only [h3210, h4010, h4095, h4175, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4177 | h4177
                · linarith only [h4089, h4093, h4094, h4095, h4177, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4179 | h4179
                  · linarith only [h1833, h4091, h4177, h4179, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4181 | h4181
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4182 | h4182
                      · linarith only [h3210, h4177, h4182, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4184 | h4184
                        · linarith only [h1833, h3210, h4179, h4184, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4186 | h4186
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4187 | h4187
                            · rcases h0bigk with h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c | h4188c
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [hlam, p4188_0]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h0, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h1833, hlam, p4188_0]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h2722, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h3122, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h0, h4175, h4186, hc01, hc24, hlam, hphi, ht12, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [hlam, p4188_0]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h0, h4175, h4182, h4186, hc03, hc34, hlam, hphi, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h3211, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h4010, hlam, p4188_0]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h1833, h4094, h4175, h4182, h4186, hc01, hc34, hlam, hphi, ht12, ht23, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h3210, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [hlam, p4188_0]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h4089, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h4091, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                rcases p4188_3 (m.d 0 1) (by simp) with h4204 | h4204
                                · linarith only [h2722, h4204, hlam]
                                · rcases p4188_3 (m.d 0 2) (by simp) with h4206 | h4206
                                  · linarith only [h3211, h4206, hlam]
                                  · linarith only [h0, h4206, hlam]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h3210, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4188_1, u0elo3]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                rcases p4188_3 (m.d 0 1) (by simp) with h4210 | h4210
                                · linarith only [h2722, h4210, hlam]
                                · rcases p4188_3 (m.d 0 2) (by simp) with h4212 | h4212
                                  · linarith only [h3211, h4212, hlam]
                                  · linarith only [h3210, h4212, hlam]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [hlam, p4188_0]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p4188_1, u0elo3, u5ehi0]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                rcases p4188_3 (m.d 0 1) (by simp) with h4217 | h4217
                                · linarith only [h3122, h4217, hlam]
                                · rcases p4188_3 (m.d 0 2) (by simp) with h4219 | h4219
                                  · linarith only [h4010, h4219, hlam]
                                  · linarith only [h0, h4219, hlam]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h3210, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4188_1, u0elo4]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                rcases p4188_3 (m.d 0 1) (by simp) with h4223 | h4223
                                · linarith only [h3122, h4223, hlam]
                                · rcases p4188_3 (m.d 0 2) (by simp) with h4225 | h4225
                                  · linarith only [h4010, h4225, hlam]
                                  · linarith only [h3210, h4225, hlam]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [h4093, hlam, p4188_1]
                              · have p4188_0 := h4188c.1
                                have p4188_1 := h4188c.2.1
                                have p4188_2 := h4188c.2.2.1
                                have p4188_3 := h4188c.2.2.2
                                linarith only [hlam, p4188_0]
                            · linarith only [h0, h4175, h4182, h4186, h4187, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h2722, h4093, h4095, h4186, hlam]
                    · linarith only [h2722, h4093, h4181, hlam]
          · linarith only [h0, h3210, h4094, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4234 | h4234
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4235 | h4235
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4236 | h4236
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4237 | h4237
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4238 | h4238
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4239 | h4239
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4240 | h4240
                      · linarith only [h1833, h3210, h3211, h4089, h4093, h4234, h4237, h4239, h4240, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4242 | h4242
                        · linarith only [h3210, h3211, h4093, h4234, h4237, h4239, h4242, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4244 | h4244
                          · linarith only [h3210, h3211, h4093, h4234, h4237, h4240, h4244, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h3210, h3211, h4244, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h3210, h3211, h4235, h4239, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1833, h4089, h4237, h4238, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4249 | h4249
                  · linarith only [h1833, h4091, h4237, h4249, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4251 | h4251
                    · linarith only [h3210, h3211, h4093, h4237, h4251, hc23, hc34, hlam, hphi]
                    · linarith only [h3210, h3211, h4235, h4251, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h3210, h3211, h4235, h4236, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4255 | h4255
              · linarith only [h3210, h4010, h4235, h4255, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4257 | h4257
                · linarith only [h1833, h4089, h4234, h4235, h4257, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4259 | h4259
                  · linarith only [h1833, h4091, h4257, h4259, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4261 | h4261
                    · linarith only [h3210, h3211, h4093, h4257, h4261, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4263 | h4263
                      · linarith only [h0, h3210, h4235, h4261, h4263, hc34, hc45, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4265 | h4265
                        · linarith only [h0, h1833, h3210, h4235, h4259, h4261, h4265, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4267 | h4267
                          · linarith only [h0, h3210, h4235, h4261, h4263, h4267, hc23, hc34, hlam, hphi]
                          · linarith only [h3210, h3211, h4267, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h3210, h3211, h4234, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3210 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 4 (by decide) (by decide) with h3211 | h3211
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122 h3210 h3211
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1833 h2722 h3122 h3210 h3211

set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_R_s1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1833 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2722 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3122 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3210 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4271 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1833 := hg1833
  rcases m.htr 0 2 5 (by decide) (by decide) with h4272 | h4272
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4273 | h4273
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4274 | h4274
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4275 | h4275
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4276 | h4276
          · linarith only [h3210, h4272, h4276, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4278 | h4278
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4279 | h4279
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4280 | h4280
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4281 | h4281
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4282 | h4282
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4283 | h4283
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4284 | h4284
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4285 | h4285
                          · linarith only [h4271, h4285, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4287 | h4287
                            · linarith only [h4283, h4285, h4287, hlam]
                            · rcases h0bigk with h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c | h4289c
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h0, hlam, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h1833, hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h2722, hlam, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h3122, hlam, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h0, h4276, hc01, hc23, hlam, hphi, ht12, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h3210, hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h0, h4275, h4276, h4283, h4285, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h0, h4276, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4289_1, u5ehi0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                rcases p4289_3 (m.d 0 1) (by simp) with h4300 | h4300
                                · linarith only [h1833, h4300, hlam]
                                · rcases p4289_3 (m.d 0 2) (by simp) with h4302 | h4302
                                  · linarith only [h3210, h4302, hlam]
                                  · linarith only [h0, h4302, hlam]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h4271, h4283, hc34, hlam, hphi, ht0b, ht45, ht5b, p4289_1, u0elo2]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h4275, h4283, h4285, hc34, hlam, hphi, ht0b, ht45, ht5b, p4289_1, u0elo2]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p4289_1, u0elo2, u5ehi0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h0, h4271, h4276, hc01, hc23, hlam, hphi, ht12, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h4271, hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h4273, hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h0, h4271, h4272, h4276, h4284, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4289_1, u5ehi3]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h0, h4272, h4276, hc01, hc23, hlam, hphi, ht12, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h4272, hlam, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h4274, hlam, p4289_0]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [h4275, hlam, p4289_1]
                              · have p4289_0 := h4289c.1
                                have p4289_1 := h4289c.2.1
                                have p4289_2 := h4289c.2.2.1
                                have p4289_3 := h4289c.2.2.2
                                linarith only [hlam, p4289_0]
                        · linarith only [h0, h4271, h4275, h4276, h4284, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h0, h4271, h4275, h4276, h4283, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · linarith only [h2722, h4275, h4282, hlam]
                  · linarith only [h1833, h4274, h4281, hlam]
                · linarith only [h1833, h4273, h4280, hlam]
              · linarith only [h0, h4272, h4279, hlam]
            · linarith only [h0, h4271, h4278, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4326 | h4326
          · linarith only [h3210, h4272, h4326, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4328 | h4328
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4329 | h4329
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4330 | h4330
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4331 | h4331
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4332 | h4332
                    · linarith only [h2722, h4275, h4326, h4328, h4332, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4334 | h4334
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4335 | h4335
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4336 | h4336
                          · linarith only [h4271, h4336, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4338 | h4338
                            · linarith only [h0, h2722, h4272, h4326, h4332, h4334, h4336, h4338, hc01, hc23, hlam, hphi, ht12]
                            · rcases h0bigk with h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c | h4340c
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h0, hlam, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h1833, hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h2722, hlam, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h3122, hlam, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h0, h4326, hc01, hc23, hlam, hphi, ht12, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h3210, hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h0, h2722, h4326, hc01, hc23, hlam, hphi, ht12, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h0, h4326, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4340_1, u5ehi0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                rcases p4340_3 (m.d 0 1) (by simp) with h4351 | h4351
                                · linarith only [h1833, h4351, hlam]
                                · rcases p4340_3 (m.d 0 2) (by simp) with h4353 | h4353
                                  · linarith only [h3210, h4353, hlam]
                                  · linarith only [h0, h4353, hlam]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h4272, hlam, hphi, ht0b, ht5b, p4340_1, u0elo2, u5ehi2]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                rcases p4340_3 (m.d 0 1) (by simp) with h4358 | h4358
                                · linarith only [h1833, h4358, hlam]
                                · rcases p4340_3 (m.d 0 2) (by simp) with h4360 | h4360
                                  · linarith only [h3210, h4360, hlam]
                                  · linarith only [h4271, h4360, hlam]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h4272, h4335, hlam, hphi, ht0b, ht5b, p4340_1, u0elo2, u5ehi3]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h2722, h4332, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h4271, hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h4273, hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h4275, hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h0, h4272, h4326, hc01, hc23, hlam, hphi, ht12, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h4272, hlam, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h4274, hlam, p4340_0]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [h0, h2722, h4272, h4326, hc01, hc23, hlam, hphi, ht12, p4340_1]
                              · have p4340_0 := h4340c.1
                                have p4340_1 := h4340c.2.1
                                have p4340_2 := h4340c.2.2.1
                                have p4340_3 := h4340c.2.2.2
                                linarith only [hlam, p4340_0]
                        · linarith only [h0, h4326, h4335, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h4272, h4326, h4334, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                  · linarith only [h1833, h4274, h4331, hlam]
                · linarith only [h1833, h4273, h4274, h4330, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
              · linarith only [h0, h4272, h4329, hlam]
            · linarith only [h0, h4271, h4328, hlam]
      · linarith only [h3210, h4272, h4274, hlam]
    · linarith only [h3210, h4271, h4273, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4382 | h4382
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4383 | h4383
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4384 | h4384
        · linarith only [h4271, h4272, h4384, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4386 | h4386
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4387 | h4387
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4388 | h4388
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4389 | h4389
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4390 | h4390
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4391 | h4391
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4392 | h4392
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4393 | h4393
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4394 | h4394
                          · linarith only [h4271, h4272, h4384, h4386, h4393, h4394, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4396 | h4396
                            · linarith only [h4271, h4272, h4392, h4394, h4396, hlam]
                            · rcases h0bigk with h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c | h4398c
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h0, hlam, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h1833, hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h2722, hlam, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h3122, hlam, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h4272, h4386, h4389, h4391, h4394, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h3210, hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h2722, h4272, h4386, h4389, h4391, h4394, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h4272, hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h3210, h4386, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h3210, h4271, h4386, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h2722, h3210, h4386, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h3210, h4386, hc12, hlam, hphi, ht01, ht0b, ht5b, p4398_1, u5ehi0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h3210, h4271, h4386, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h4271, hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h4382, hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h4384, hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h4272, h4386, h4389, h4391, h4394, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h0, h4272, h4386, h4389, h4391, h4394, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h4383, hlam, p4398_0]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [h2722, h4272, h4386, h4389, h4391, h4394, hc01, hc12, hlam, hphi, p4398_1]
                              · have p4398_0 := h4398c.1
                                have p4398_1 := h4398c.2.1
                                have p4398_2 := h4398c.2.2.1
                                have p4398_3 := h4398c.2.2.2
                                linarith only [hlam, p4398_0]
                        · linarith only [h3210, h4383, h4393, hlam]
                      · linarith only [h3210, h4382, h4392, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4426 | h4426
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4427 | h4427
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4428 | h4428
                          · linarith only [h4271, h4391, h4428, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4430 | h4430
                            · linarith only [h2722, h4391, h4430, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c | h4432c
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h0, hlam, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h1833, hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h2722, hlam, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h3122, hlam, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4272, h4386, h4427, hc01, hc12, hlam, hphi, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h3210, hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h2722, h4272, h4386, h4427, hc01, hc12, hlam, hphi, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4272, hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h3210, h4386, hc01, hc12, hlam, hphi, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h3210, h4271, h4386, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h2722, h3210, h4386, hc01, hc12, hlam, hphi, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h3210, h4386, hc12, hlam, hphi, ht01, ht0b, ht5b, p4432_1, u5ehi0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h2722, h4391, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4271, hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4382, hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4384, hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4272, h4386, h4427, hc01, hc12, hlam, hphi, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4271, h4272, h4386, h4426, h4427, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h4383, hlam, p4432_0]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [h2722, h4272, h4386, h4427, hc01, hc12, hlam, hphi, p4432_1]
                              · have p4432_0 := h4432c.1
                                have p4432_1 := h4432c.2.1
                                have p4432_2 := h4432c.2.2.1
                                have p4432_3 := h4432c.2.2.2
                                linarith only [hlam, p4432_0]
                        · linarith only [h3210, h4383, h4427, hlam]
                      · linarith only [h3210, h4382, h4426, hlam]
                  · linarith only [h1833, h4383, h4390, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h3210, h4382, h4383, h4386, h4389, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
              · linarith only [h3210, h4271, h4386, h4388, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h3210, h4271, h4386, h4387, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4464 | h4464
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4465 | h4465
              · linarith only [h4271, h4272, h4386, h4465, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4467 | h4467
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4468 | h4468
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4469 | h4469
                    · linarith only [h2722, h4384, h4386, h4464, h4469, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4471 | h4471
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4472 | h4472
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4473 | h4473
                          · linarith only [h4271, h4469, h4473, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4475 | h4475
                            · linarith only [h0, h4465, h4473, h4475, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c | h4477c
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, hlam, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h1833, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h2722, hlam, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3122, hlam, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, h4465, hc01, hc25, hlam, hphi, ht12, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h3210, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, h2722, h4465, h4473, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4272, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                rcases p4477_3 (m.d 0 1) (by simp) with h4488 | h4488
                                · linarith only [h1833, h4488, hlam]
                                · rcases p4477_3 (m.d 0 2) (by simp) with h4490 | h4490
                                  · linarith only [h3210, h4490, hlam]
                                  · linarith only [h0, h4490, hlam]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4271, hc24, hlam, hphi, ht0b, ht45, ht5b, p4477_1, u0elo2]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                rcases p4477_3 (m.d 0 1) (by simp) with h4495 | h4495
                                · linarith only [h1833, h4495, hlam]
                                · rcases p4477_3 (m.d 0 2) (by simp) with h4497 | h4497
                                  · linarith only [h3210, h4497, hlam]
                                  · linarith only [h4271, h4497, hlam]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht5b, p4477_1, u0elo2, u5ehi0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h0, h4271, h4465, h4473, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4477_1]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4271, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4382, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4384, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                rcases p4477_3 (m.d 0 1) (by simp) with h4506 | h4506
                                · linarith only [h3122, h4506, hlam]
                                · rcases p4477_3 (m.d 0 2) (by simp) with h4508 | h4508
                                  · linarith only [h4272, h4508, hlam]
                                  · linarith only [h0, h4508, hlam]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4271, h4471, hc34, hlam, hphi, ht0b, ht45, ht5b, p4477_1, u0elo4]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [h4383, hlam, p4477_0]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                rcases p4477_3 (m.d 0 1) (by simp) with h4513 | h4513
                                · linarith only [h3122, h4513, hlam]
                                · rcases p4477_3 (m.d 0 2) (by simp) with h4515 | h4515
                                  · linarith only [h4272, h4515, hlam]
                                  · linarith only [h4271, h4515, hlam]
                              · have p4477_0 := h4477c.1
                                have p4477_1 := h4477c.2.1
                                have p4477_2 := h4477c.2.2.1
                                have p4477_3 := h4477c.2.2.2
                                linarith only [hlam, p4477_0]
                        · linarith only [h3210, h4383, h4472, hlam]
                      · linarith only [h0, h4386, h4471, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1833, h4383, h4468, hlam]
                · linarith only [h1833, h4382, h4383, h4467, hlam, hphi, ht0b, ht5b, u0elo3, u5ehi3]
            · linarith only [h0, h4271, h4464, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4524 | h4524
        · linarith only [h3210, h4271, h4383, h4524, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4526 | h4526
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4527 | h4527
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4528 | h4528
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4529 | h4529
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4530 | h4530
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4531 | h4531
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4532 | h4532
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4533 | h4533
                        · linarith only [h3210, h4271, h4383, h4526, h4533, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h3210, h4271, h4526, h4530, h4532, h4533, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h3210, h4382, h4532, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4537 | h4537
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4538 | h4538
                        · linarith only [h1833, h4383, h4526, h4538, hc01, hc12, hlam, hphi]
                        · linarith only [h3210, h4271, h4526, h4530, h4537, h4538, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h3210, h4382, h4537, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4542 | h4542
                    · linarith only [h2722, h4524, h4529, h4530, h4542, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4544 | h4544
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4545 | h4545
                        · linarith only [h4526, h4530, h4545, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4547 | h4547
                          · linarith only [h4271, h4272, h4528, h4542, h4547, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4549 | h4549
                            · linarith only [h2722, h3210, h4271, h4526, h4530, h4542, h4544, h4549, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h3210, h4271, h4526, h4530, h4544, h4549, hc34, hc45, hlam, hphi]
                      · linarith only [h3210, h4382, h4544, hlam]
                · linarith only [h3210, h4271, h4382, h4526, h4529, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h3210, h4271, h4526, h4528, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h3210, h4271, h4526, h4527, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4556 | h4556
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4557 | h4557
              · linarith only [h4272, h4526, h4557, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4559 | h4559
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4560 | h4560
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4561 | h4561
                    · linarith only [h2722, h4524, h4526, h4556, h4561, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4563 | h4563
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4564 | h4564
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4565 | h4565
                          · linarith only [h4271, h4561, h4565, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4567 | h4567
                            · linarith only [h3210, h4271, h4383, h4526, h4557, h4560, h4563, h4565, h4567, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c | h4569c
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h0, hlam, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h1833, hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h2722, hlam, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h3122, hlam, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h3210, h4383, h4526, h4560, hc01, hc23, hlam, hphi, ht12, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h3210, hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h2722, h3210, h4383, h4526, h4560, hc01, hc23, hlam, hphi, ht12, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4272, hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4383, h4526, h4560, hc01, hc23, hlam, hphi, ht12, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4271, h4383, h4526, h4560, h4563, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h2722, h4383, h4526, h4560, hc01, hc23, hlam, hphi, ht12, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4383, hlam, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h2722, h4556, h4557, hc01, hc25, hlam, hphi, ht12, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4271, hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4382, hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4524, hlam, p4569_0]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4383, h4526, h4560, hc01, hc23, hlam, hphi, ht12, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h4271, h4563, hc34, hlam, hphi, ht0b, ht45, ht5b, p4569_1, u0elo4]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h3210, h4271, h4383, h4526, h4560, h4563, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [h2722, h4383, h4526, h4560, hc01, hc23, hlam, hphi, ht12, p4569_1]
                              · have p4569_0 := h4569c.1
                                have p4569_1 := h4569c.2.1
                                have p4569_2 := h4569c.2.2.1
                                have p4569_3 := h4569c.2.2.2
                                linarith only [hlam, p4569_0]
                        · linarith only [h4526, h4560, h4564, hlam]
                      · linarith only [h1833, h4382, h4526, h4563, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4597 | h4597
                    · linarith only [h2722, h4524, h4526, h4556, h4560, h4597, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4599 | h4599
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4600 | h4600
                        · linarith only [h0, h4526, h4560, h4600, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h2722, h4526, h4556, h4600, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h2722, h4526, h4556, h4599, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h1833, h2722, h4382, h4526, h4556, h4559, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h3210, h4271, h4383, h4556, hc12, hc35, hlam, hphi, ht23]
    · linarith only [h3210, h4271, h4382, hlam]

end R2N4
