import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5526000 in
set_option maxHeartbeats 5526000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_M_IR_s5_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3977 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3978 | h3978
  · rcases m.htr 0 1 5 (by decide) (by decide) with h3979 | h3979
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3980 | h3980
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3981 | h3981
        · rcases m.htr 0 2 5 (by decide) (by decide) with h3982 | h3982
          · rcases m.htr 0 3 4 (by decide) (by decide) with h3983 | h3983
            · rcases m.htr 0 3 5 (by decide) (by decide) with h3984 | h3984
              · rcases m.htr 0 4 5 (by decide) (by decide) with h3985 | h3985
                · rcases m.htr 1 2 3 (by decide) (by decide) with h3986 | h3986
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h3987 | h3987
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h3988 | h3988
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h3989 | h3989
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3990 | h3990
                          · linarith only [h0, h3977, h3990, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h3977, h3984, h3989, h3990, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h3993 | h3993
                          · linarith only [h0, h3977, h3993, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h3995 | h3995
                            · linarith only [h0, h3977, h3983, h3989, h3995, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h3997 | h3997
                              · linarith only [h0, h3978, h3985, h3986, h3989, h3995, h3997, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h3999 | h3999
                                · linarith only [h0, h3977, h3983, h3985, h3986, h3989, h3995, h3999, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4001 | h4001
                                  · linarith only [h3987, h3995, h4001, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4003 | h4003
                                    · linarith only [h0, h3977, h3983, h3989, h3995, h4003, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h0, h3977, h3983, h3985, h3986, h3989, h4003, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3977, h3984, h3988, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h3977, h3983, h3985, h3987, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h3977, h3983, h3985, h3986, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4009 | h4009
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4010 | h4010
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4011 | h4011
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4012 | h4012
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4013 | h4013
                          · linarith only [h0, h3977, h4013, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h0, h3977, h3984, h4012, h4013, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4016 | h4016
                          · linarith only [h0, h3977, h4016, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4018 | h4018
                            · linarith only [h0, h3977, h3983, h3985, h4012, h4018, hc12, hlam, hphi, ht01, u0ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4020 | h4020
                              · linarith only [h4009, h4012, h4020, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4022 | h4022
                                · linarith only [h0, h3977, h3983, h4009, h4012, h4016, h4018, h4022, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4024 | h4024
                                  · linarith only [h3985, h4024, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4026 | h4026
                                    · linarith only [h0, h3977, h3983, h3985, h4026, hc12, hlam, hphi, ht01, u0ehi3]
                                    · rcases h2bigk with h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c | h4028c
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h0, hlam, p4028_1]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        rcases p4028_3 (m.d 0 2) (by simp) with h4031 | h4031
                                        · rcases p4028_3 (m.d 1 2) (by simp) with h4032 | h4032
                                          · rcases p4028_3 (m.d 2 3) (by simp) with h4033 | h4033
                                            · linarith only [h4033, hlam, p4028_0]
                                            · rcases p4028_3 (m.d 2 4) (by simp) with h4035 | h4035
                                              · linarith only [h3981, h4035, hlam]
                                              · linarith only [h4020, h4035, hlam]
                                          · linarith only [h4009, h4032, hlam]
                                        · linarith only [h4031, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        rcases p4028_3 (m.d 0 2) (by simp) with h4040 | h4040
                                        · rcases p4028_3 (m.d 1 2) (by simp) with h4041 | h4041
                                          · rcases p4028_3 (m.d 2 3) (by simp) with h4042 | h4042
                                            · linarith only [h3980, h4042, hlam]
                                            · rcases p4028_3 (m.d 2 4) (by simp) with h4044 | h4044
                                              · linarith only [h4044, hlam, p4028_0]
                                              · rcases p4028_3 (m.d 2 5) (by simp) with h4046 | h4046
                                                · linarith only [h3982, h4046, hlam]
                                                · linarith only [h4024, h4046, hlam]
                                          · linarith only [h4010, h4041, hlam]
                                        · linarith only [h4040, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        rcases p4028_3 (m.d 0 2) (by simp) with h4051 | h4051
                                        · rcases p4028_3 (m.d 1 2) (by simp) with h4052 | h4052
                                          · rcases p4028_3 (m.d 2 3) (by simp) with h4053 | h4053
                                            · linarith only [h3980, h4053, hlam]
                                            · rcases p4028_3 (m.d 2 4) (by simp) with h4055 | h4055
                                              · linarith only [h3981, h4055, hlam]
                                              · rcases p4028_3 (m.d 2 5) (by simp) with h4057 | h4057
                                                · linarith only [h4057, hlam, p4028_0]
                                                · rcases h3bigk with h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c | h4059c
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    rcases p4059_3 (m.d 0 3) (by simp) with h4061 | h4061
                                                    · rcases p4059_3 (m.d 1 3) (by simp) with h4062 | h4062
                                                      · linarith only [h3977, h4062, hlam]
                                                      · rcases p4059_3 (m.d 2 3) (by simp) with h4064 | h4064
                                                        · linarith only [h3980, h4064, hlam]
                                                        · rcases p4059_3 (m.d 3 4) (by simp) with h4066 | h4066
                                                          · linarith only [h3983, h4066, hlam]
                                                          · linarith only [h4012, h4066, hlam]
                                                    · linarith only [h3977, h4061, hlam]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    rcases p4059_3 (m.d 0 3) (by simp) with h4070 | h4070
                                                    · rcases p4059_3 (m.d 1 3) (by simp) with h4071 | h4071
                                                      · linarith only [h3977, h4071, hlam]
                                                      · linarith only [h4009, h4071, hlam]
                                                    · linarith only [h3980, h4070, hlam]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h0, h3977, h4009, h4012, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h0, h3977, hc12, hlam, hphi, ht01, ht0b, ht5b, p4059_1, u5ehi3]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h3977, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h4012, hc23, hc34, hlam, hphi, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h4012, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h4016, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h3980, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h4009, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h4020, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h4022, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h3983, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h0, h3977, h3983, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h0, h3977, h3983, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h4026, hlam, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h3984, hlam, p4059_0]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h0, h3977, h3984, h4009, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h0, h3977, h3984, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [h0, h3977, h3984, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4059_1]
                                                  · have p4059_0 := h4059c.1
                                                    have p4059_1 := h4059c.2.1
                                                    have p4059_2 := h4059c.2.2.1
                                                    have p4059_3 := h4059c.2.2.2
                                                    linarith only [hlam, p4059_0]
                                          · linarith only [h4011, h4052, hlam]
                                        · linarith only [h4051, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, p4028_1, u0ehi1]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h0, h3977, h3983, h4009, h4012, hlam, p4028_2]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        rcases p4028_3 (m.d 0 2) (by simp) with h4102 | h4102
                                        · linarith only [h0, h4102, hlam]
                                        · linarith only [h3981, h4102, hlam]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        rcases p4028_3 (m.d 0 2) (by simp) with h4105 | h4105
                                        · linarith only [h0, h4105, hlam]
                                        · linarith only [h3982, h4105, hlam]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h3980, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h4009, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h4020, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h4022, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h3981, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h4010, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h0, h3978, h4010, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4028_1]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h4024, hlam, p4028_1]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h3982, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h4011, hlam, p4028_0]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h0, h3979, h4011, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4028_1]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [h0, h3977, h3984, h4011, h4016, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4028_1]
                                      · have p4028_0 := h4028c.1
                                        have p4028_1 := h4028c.2.1
                                        have p4028_2 := h4028c.2.2.1
                                        have p4028_3 := h4028c.2.2.2
                                        linarith only [hlam, p4028_0]
                      · linarith only [h0, h3977, h3984, h4011, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h3977, h3984, h3985, h4010, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h0, h3977, h3984, h3985, h4009, hc23, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4126 | h4126
                · linarith only [h3983, h3984, h4126, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4128 | h4128
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4129 | h4129
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4130 | h4130
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4131 | h4131
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4132 | h4132
                          · linarith only [h3977, h3983, h3984, h4132, hc01, hlam, hphi, u0ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4134 | h4134
                            · linarith only [h0, h3979, h4126, h4131, h4132, h4134, hc12, hlam, hphi, ht01, u0ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4136 | h4136
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4137 | h4137
                                · linarith only [h3983, h3984, h4137, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4139 | h4139
                                  · linarith only [h0, h3979, h4126, h4128, h4132, h4136, h4139, hc12, hlam, hphi, ht01, u0ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4141 | h4141
                                    · linarith only [h4126, h4141, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                                    · rcases h2bigk with h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c | h4143c
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h0, hlam, p4143_1]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        rcases p4143_3 (m.d 0 2) (by simp) with h4146 | h4146
                                        · rcases p4143_3 (m.d 1 2) (by simp) with h4147 | h4147
                                          · rcases p4143_3 (m.d 2 3) (by simp) with h4148 | h4148
                                            · linarith only [h4148, hlam, p4143_0]
                                            · rcases p4143_3 (m.d 2 4) (by simp) with h4150 | h4150
                                              · linarith only [h3981, h4150, hlam]
                                              · rcases p4143_3 (m.d 2 5) (by simp) with h4152 | h4152
                                                · linarith only [h3982, h4152, hlam]
                                                · linarith only [h4137, h4152, hlam]
                                          · linarith only [h4128, h4147, hlam]
                                        · linarith only [h4146, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        rcases p4143_3 (m.d 0 2) (by simp) with h4157 | h4157
                                        · rcases p4143_3 (m.d 1 2) (by simp) with h4158 | h4158
                                          · rcases p4143_3 (m.d 2 3) (by simp) with h4159 | h4159
                                            · linarith only [h3980, h4159, hlam]
                                            · linarith only [h4136, h4159, hlam]
                                          · linarith only [h4129, h4158, hlam]
                                        · linarith only [h4157, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        rcases p4143_3 (m.d 0 2) (by simp) with h4164 | h4164
                                        · rcases p4143_3 (m.d 1 2) (by simp) with h4165 | h4165
                                          · rcases p4143_3 (m.d 2 3) (by simp) with h4166 | h4166
                                            · linarith only [h3980, h4166, hlam]
                                            · rcases p4143_3 (m.d 2 4) (by simp) with h4168 | h4168
                                              · linarith only [h3981, h4168, hlam]
                                              · rcases p4143_3 (m.d 2 5) (by simp) with h4170 | h4170
                                                · linarith only [h4170, hlam, p4143_0]
                                                · rcases h3bigk with h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c | h4172c
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3984, h4141, hc13, hc45, hlam, hphi, ht34, p4172_1]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3984, h4136, h4141, hc34, hc45, hlam, hphi, p4172_1]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3984, h4141, hc34, hc45, hlam, hphi, p4172_1]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3984, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3977, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h0, h3977, h3983, h3984, h4136, h4141, hc12, hc34, hc45, hlam, hphi, ht01, p4172_1, u0ehi3]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h0, h3977, h3983, h3984, h4141, hc12, hc34, hc45, hlam, hphi, ht01, p4172_1, u0ehi3]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4132, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3980, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4128, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3980, h3984, h4141, hc34, hc45, hlam, hphi, p4172_1]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4137, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3983, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4131, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4136, hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [hlam, p4172_0]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4141, hlam, p4172_1]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h3983, h4141, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p4172_1, u0ehi3]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4131, h4141, hc34, hc45, hlam, hphi, p4172_1]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [h4136, h4141, hc34, hc45, hlam, hphi, p4172_1]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    rcases p4172_3 (m.d 0 3) (by simp) with h4196 | h4196
                                                    · linarith only [h3984, h4196, hlam]
                                                    · linarith only [h3983, h4196, hlam]
                                                  · have p4172_0 := h4172c.1
                                                    have p4172_1 := h4172c.2.1
                                                    have p4172_2 := h4172c.2.2.1
                                                    have p4172_3 := h4172c.2.2.2
                                                    linarith only [hlam, p4172_0]
                                          · linarith only [h4130, h4165, hlam]
                                        · linarith only [h4164, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, p4143_1, u0ehi1]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        rcases p4143_3 (m.d 0 2) (by simp) with h4204 | h4204
                                        · linarith only [h0, h4204, hlam]
                                        · linarith only [h3980, h4204, hlam]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        rcases p4143_3 (m.d 0 2) (by simp) with h4207 | h4207
                                        · linarith only [h0, h4207, hlam]
                                        · linarith only [h3981, h4207, hlam]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        rcases p4143_3 (m.d 0 2) (by simp) with h4210 | h4210
                                        · linarith only [h0, h4210, hlam]
                                        · linarith only [h3982, h4210, hlam]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h3980, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h4128, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h0, h3977, h4128, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4143_1]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h4137, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h3981, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h4129, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h4136, hlam, p4143_1]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h4139, hlam, p4143_1]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h3982, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h4130, hlam, p4143_0]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h0, h3979, h3983, h3984, h4130, h4141, hc12, hc23, hc45, hlam, hphi, ht01, ht34, p4143_1, u0ehi3]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [h0, h3979, h3983, h3984, h4130, h4136, h4141, hc12, hc34, hc45, hlam, hphi, ht01, p4143_1, u0ehi3]
                                      · have p4143_0 := h4143c.1
                                        have p4143_1 := h4143c.2.1
                                        have p4143_2 := h4143c.2.2.1
                                        have p4143_3 := h4143c.2.2.2
                                        linarith only [hlam, p4143_0]
                              · linarith only [h3983, h3984, h4136, hc23, hc35, hlam, hphi]
                        · linarith only [h3983, h3984, h4131, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h3979, h4130, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h4129, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h3979, h3983, h3984, h4128, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4233 | h4233
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4234 | h4234
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4235 | h4235
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4236 | h4236
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4237 | h4237
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4238 | h4238
                        · linarith only [h3977, h3983, h4233, h4238, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4240 | h4240
                          · linarith only [h0, h3978, h4238, h4240, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h3983, h4233, h4235, h4240, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h3979, h4237, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h3978, h3983, h4233, h4236, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3978, h3983, h4233, h4235, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h3983, h4233, h4234, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4247 | h4247
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4248 | h4248
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4249 | h4249
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4250 | h4250
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4251 | h4251
                        · linarith only [h3983, h4251, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4253 | h4253
                          · linarith only [h3978, h4233, h4251, h4253, hc01, hlam, hphi, u0ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4255 | h4255
                            · linarith only [h0, h3978, h4255, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4257 | h4257
                              · linarith only [h0, h3978, h3983, h4247, h4248, h4251, h4255, h4257, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4259 | h4259
                                · linarith only [h0, h3978, h4233, h4247, h4248, h4251, h4255, h4259, hc12, hlam, hphi, ht01, u0ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4261 | h4261
                                  · linarith only [h4249, h4255, h4261, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4263 | h4263
                                    · rcases h2bigk with h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c | h4264c
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h0, hlam, p4264_1]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        rcases p4264_3 (m.d 0 2) (by simp) with h4267 | h4267
                                        · rcases p4264_3 (m.d 1 2) (by simp) with h4268 | h4268
                                          · rcases p4264_3 (m.d 2 3) (by simp) with h4269 | h4269
                                            · linarith only [h4269, hlam, p4264_0]
                                            · rcases p4264_3 (m.d 2 4) (by simp) with h4271 | h4271
                                              · linarith only [h3981, h4271, hlam]
                                              · linarith only [h4257, h4271, hlam]
                                          · linarith only [h4248, h4268, hlam]
                                        · linarith only [h4267, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        rcases p4264_3 (m.d 0 2) (by simp) with h4276 | h4276
                                        · rcases p4264_3 (m.d 1 2) (by simp) with h4277 | h4277
                                          · rcases p4264_3 (m.d 2 3) (by simp) with h4278 | h4278
                                            · linarith only [h3980, h4278, hlam]
                                            · rcases p4264_3 (m.d 2 4) (by simp) with h4280 | h4280
                                              · linarith only [h4280, hlam, p4264_0]
                                              · rcases p4264_3 (m.d 2 5) (by simp) with h4282 | h4282
                                                · linarith only [h3982, h4282, hlam]
                                                · linarith only [h4261, h4282, hlam]
                                          · linarith only [h4249, h4277, hlam]
                                        · linarith only [h4276, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        rcases p4264_3 (m.d 0 2) (by simp) with h4287 | h4287
                                        · rcases p4264_3 (m.d 1 2) (by simp) with h4288 | h4288
                                          · rcases p4264_3 (m.d 2 3) (by simp) with h4289 | h4289
                                            · linarith only [h3980, h4289, hlam]
                                            · rcases p4264_3 (m.d 2 4) (by simp) with h4291 | h4291
                                              · linarith only [h3981, h4291, hlam]
                                              · rcases p4264_3 (m.d 2 5) (by simp) with h4293 | h4293
                                                · linarith only [h4293, hlam, p4264_0]
                                                · rcases h3bigk with h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c | h4295c
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4233, h4248, h4263, hc23, hc34, hlam, hphi, p4295_1]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4233, h4263, hc23, hc34, hlam, hphi, p4295_1]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h3983, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4233, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h3977, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h0, h3978, h4247, h4251, h4255, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4295_1]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4251, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4253, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h3980, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4248, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4257, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4259, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p4295_1, u0ehi2]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    rcases p4295_3 (m.d 0 3) (by simp) with h4312 | h4312
                                                    · linarith only [h3983, h4312, hlam]
                                                    · linarith only [h3977, h4312, hlam]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    rcases p4295_3 (m.d 0 3) (by simp) with h4315 | h4315
                                                    · linarith only [h3983, h4315, hlam]
                                                    · linarith only [h3980, h4315, hlam]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h0, h3978, h4233, h4247, h4248, h4251, h4255, hc12, hc23, hc34, hlam, hphi, ht01, p4295_1, u0ehi2]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h0, h3978, h4247, h4248, h4251, h4255, hc12, hc23, hc35, hlam, hphi, ht01, p4295_1, u0ehi2]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    rcases p4295_3 (m.d 0 3) (by simp) with h4321 | h4321
                                                    · linarith only [h4233, h4321, hlam]
                                                    · linarith only [h3977, h4321, hlam]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    rcases p4295_3 (m.d 0 3) (by simp) with h4324 | h4324
                                                    · linarith only [h4233, h4324, hlam]
                                                    · linarith only [h3980, h4324, hlam]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [h4263, hlam, p4295_0]
                                                  · have p4295_0 := h4295c.1
                                                    have p4295_1 := h4295c.2.1
                                                    have p4295_2 := h4295c.2.2.1
                                                    have p4295_3 := h4295c.2.2.2
                                                    linarith only [hlam, p4295_0]
                                          · linarith only [h4250, h4288, hlam]
                                        · linarith only [h4287, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, p4264_1, u0ehi1]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h0, h3978, h4247, h4248, h4251, h4255, hlam, p4264_2]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h0, h3978, h4247, h4249, h4255, hlam, p4264_2]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        rcases p4264_3 (m.d 0 2) (by simp) with h4335 | h4335
                                        · linarith only [h0, h4335, hlam]
                                        · linarith only [h3982, h4335, hlam]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h3980, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h4248, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h4257, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h4259, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h3981, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h4249, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h0, h3978, h4247, h4249, h4255, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4264_1]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h4261, hlam, p4264_1]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h3982, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h4250, hlam, p4264_0]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h0, h3978, h4247, h4250, h4255, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4264_1]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [h0, h3978, h4247, h4250, h4255, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p4264_1]
                                      · have p4264_0 := h4264c.1
                                        have p4264_1 := h4264c.2.1
                                        have p4264_2 := h4264c.2.2.1
                                        have p4264_3 := h4264c.2.2.2
                                        linarith only [hlam, p4264_0]
                                    · linarith only [h0, h3978, h3983, h4247, h4263, hc12, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h0, h3978, h4247, h4250, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h3978, h4233, h4247, h4249, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h3978, h4233, h4247, h4248, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4357 | h4357
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4358 | h4358
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4359 | h4359
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4360 | h4360
                        · linarith only [h3977, h3983, h4360, hc01, hlam, hphi, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4362 | h4362
                          · linarith only [h0, h3978, h4360, h4362, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4364 | h4364
                            · linarith only [h0, h3978, h4364, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4366 | h4366
                              · linarith only [h0, h3979, h3983, h4357, h4360, h4364, h4366, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4368 | h4368
                                · linarith only [h0, h3979, h4233, h4357, h4360, h4364, h4368, hc12, hlam, hphi, ht01, u0ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4370 | h4370
                                  · linarith only [h0, h3979, h3983, h4247, h4358, h4364, h4370, hc12, hlam, hphi, ht01, u0ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4372 | h4372
                                    · linarith only [h3983, h4247, h4372, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                    · linarith only [h3983, h4372, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                      · linarith only [h0, h3979, h4359, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h3979, h3983, h4247, h4358, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h3979, h3983, h4247, h4357, hc23, hlam, hphi, ht01, ht12, u0ehi2]
          · linarith only [h0, h3979, h3982, hlam]
        · linarith only [h0, h3978, h3981, hlam]
      · linarith only [h0, h3977, h3980, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4381 | h4381
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4382 | h4382
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4383 | h4383
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4384 | h4384
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4385 | h4385
              · linarith only [h3977, h3979, h4385, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4387 | h4387
                · linarith only [h3977, h3979, h4384, h4387, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4389 | h4389
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4390 | h4390
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4391 | h4391
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4392 | h4392
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4393 | h4393
                          · linarith only [h3977, h3979, h4385, h4393, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4395 | h4395
                            · linarith only [h3977, h3979, h4387, h4392, h4393, h4395, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                            · linarith only [h3977, h3979, h4392, h4395, hc34, hc45, hlam, hphi]
                        · linarith only [h4384, h4385, h4389, h4392, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h3977, h4383, h4384, h4391, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h3977, h4384, h4390, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h0, h3977, h4384, h4389, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4402 | h4402
              · linarith only [h3977, h3979, h4402, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4404 | h4404
                · linarith only [h3978, h3979, h4404, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4406 | h4406
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4407 | h4407
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4408 | h4408
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4409 | h4409
                        · linarith only [h3977, h4384, h4409, hc01, hlam, hphi, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4411 | h4411
                          · linarith only [h3978, h3979, h4408, h4409, h4411, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4413 | h4413
                            · linarith only [h3978, h3979, h4404, h4411, h4413, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4415 | h4415
                              · linarith only [h3978, h3979, h4384, h4406, h4409, h4413, h4415, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4417 | h4417
                                · linarith only [h3978, h3979, h4406, h4409, h4413, h4417, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4419 | h4419
                                  · linarith only [h3978, h3979, h4407, h4413, h4419, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4421 | h4421
                                    · linarith only [h3978, h3979, h4409, h4413, h4421, hc13, hc34, hlam, hphi]
                                    · linarith only [h4384, h4421, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                      · linarith only [h0, h3978, h4384, h4408, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h0, h3978, h4384, h4407, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h3978, h4384, h4406, hc23, hlam, hphi, ht01, ht12, u0ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4427 | h4427
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4428 | h4428
              · linarith only [h0, h3977, h4383, h4428, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4430 | h4430
                · linarith only [h0, h3978, h4383, h4430, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4432 | h4432
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4433 | h4433
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4434 | h4434
                      · linarith only [h0, h4383, h4434, hc12, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h0, h3977, h4427, h4434, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                    · linarith only [h0, h3977, h4427, h4433, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h0, h3977, h4427, h4432, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4439 | h4439
              · linarith only [h0, h3977, h4383, h4439, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4441 | h4441
                · linarith only [h0, h3978, h4383, h4441, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4443 | h4443
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4444 | h4444
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4445 | h4445
                      · linarith only [h0, h3978, h4383, h4427, h4445, hc12, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h0, h3978, h4427, h4445, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h0, h3978, h4427, h4444, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h3978, h4427, h4443, hc23, hlam, hphi, ht01, ht12, u0ehi2]
        · linarith only [h0, h3978, h4382, hlam]
      · linarith only [h0, h3977, h4381, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4452 | h4452
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4453 | h4453
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4454 | h4454
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4455 | h4455
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4456 | h4456
            · linarith only [h3977, h3978, h4456, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4458 | h4458
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4459 | h4459
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4460 | h4460
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4461 | h4461
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4462 | h4462
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4463 | h4463
                        · linarith only [h3977, h4456, h4458, h4463, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4465 | h4465
                          · linarith only [h3977, h3978, h4463, h4465, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h3977, h3978, h4458, h4460, h4463, h4465, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h3977, h4458, h4462, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h4454, h4461, hlam]
                  · linarith only [h0, h3977, h4458, h4460, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h3977, h3978, h4458, h4459, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4472 | h4472
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4473 | h4473
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4474 | h4474
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4475 | h4475
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4476 | h4476
                        · linarith only [h3977, h4456, h4476, hc01, hlam, hphi, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4478 | h4478
                          · linarith only [h3977, h3978, h4458, h4476, h4478, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4480 | h4480
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4481 | h4481
                              · linarith only [h3978, h4452, h4473, h4476, h4478, h4481, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4483 | h4483
                                · linarith only [h3978, h4452, h4458, h4473, h4476, h4478, h4483, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4485 | h4485
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4486 | h4486
                                    · rcases h2bigk with h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c | h4487c
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h0, hlam, p4487_1]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        rcases p4487_3 (m.d 0 2) (by simp) with h4490 | h4490
                                        · rcases p4487_3 (m.d 1 2) (by simp) with h4491 | h4491
                                          · rcases p4487_3 (m.d 2 3) (by simp) with h4492 | h4492
                                            · linarith only [h4492, hlam, p4487_0]
                                            · rcases p4487_3 (m.d 2 4) (by simp) with h4494 | h4494
                                              · linarith only [h4454, h4494, hlam]
                                              · linarith only [h4481, h4494, hlam]
                                          · linarith only [h4473, h4491, hlam]
                                        · linarith only [h4490, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4485, hc02, hlam, hphi, ht0b, ht5b, p4487_1, u5ehi4]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        rcases p4487_3 (m.d 0 2) (by simp) with h4500 | h4500
                                        · rcases p4487_3 (m.d 1 2) (by simp) with h4501 | h4501
                                          · rcases p4487_3 (m.d 2 3) (by simp) with h4502 | h4502
                                            · linarith only [h4453, h4502, hlam]
                                            · rcases p4487_3 (m.d 2 4) (by simp) with h4504 | h4504
                                              · linarith only [h4454, h4504, hlam]
                                              · linarith only [h4485, h4504, hlam]
                                          · linarith only [h4475, h4501, hlam]
                                        · linarith only [h4500, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, p4487_1, u0ehi1]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        rcases p4487_3 (m.d 0 2) (by simp) with h4511 | h4511
                                        · linarith only [h0, h4511, hlam]
                                        · linarith only [h4453, h4511, hlam]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4485, hc12, hlam, hphi, ht01, ht0b, ht5b, p4487_1, u5ehi4]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        rcases p4487_3 (m.d 0 2) (by simp) with h4515 | h4515
                                        · linarith only [h0, h4515, hlam]
                                        · linarith only [h4455, h4515, hlam]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4453, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4473, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4481, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4483, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4454, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4474, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        rcases p4487_3 (m.d 0 2) (by simp) with h4525 | h4525
                                        · rcases p4487_3 (m.d 1 2) (by simp) with h4526 | h4526
                                          · rcases p4487_3 (m.d 2 3) (by simp) with h4527 | h4527
                                            · linarith only [h4481, h4527, hlam]
                                            · rcases p4487_3 (m.d 2 4) (by simp) with h4529 | h4529
                                              · rcases p4487_3 (m.d 2 5) (by simp) with h4530 | h4530
                                                · linarith only [h4485, h4530, hlam]
                                                · linarith only [h4483, h4530, hlam]
                                              · linarith only [h4481, h4529, hlam]
                                          · linarith only [h4473, h4526, hlam]
                                        · linarith only [h4453, h4525, hlam]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4454, hc02, hlam, hphi, ht0b, ht5b, p4487_1, u5ehi2]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4455, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4475, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h3978, h4452, h4455, h4476, hc23, hc34, hlam, hphi, p4487_1]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [h4485, hlam, p4487_0]
                                      · have p4487_0 := h4487c.1
                                        have p4487_1 := h4487c.2.1
                                        have p4487_2 := h4487c.2.2.1
                                        have p4487_3 := h4487c.2.2.2
                                        linarith only [hlam, p4487_0]
                                    · linarith only [h3978, h4452, h4476, h4478, h4486, hc13, hc45, hlam, hphi, ht34]
                                  · linarith only [h3978, h4452, h4476, h4480, h4481, h4485, hc23, hc34, hlam, hphi]
                            · linarith only [h3978, h4452, h4480, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h3978, h4452, h4474, h4475, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h4452, h4458, h4474, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h4452, h4458, h4473, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · linarith only [h3978, h4452, h4472, hlam]
          · linarith only [h3978, h4452, h4454, h4455, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4551 | h4551
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4552 | h4552
            · linarith only [h0, h3977, h4454, h4552, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4554 | h4554
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4555 | h4555
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4556 | h4556
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4557 | h4557
                    · linarith only [h0, h3977, h4454, h4554, h4557, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h3977, h4554, h4557, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h3977, h4554, h4556, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h4452, h4454, h4555, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4562 | h4562
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4563 | h4563
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4564 | h4564
                    · linarith only [h0, h4454, h4564, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h4452, h4554, h4564, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h4452, h4554, h4563, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · linarith only [h0, h4452, h4454, h4562, hlam]
          · linarith only [h0, h4452, h4551, hlam]
      · linarith only [h0, h3977, h4453, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4571 | h4571
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4572 | h4572
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4573 | h4573
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4574 | h4574
            · linarith only [h3977, h3978, h4574, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4576 | h4576
              · linarith only [h3977, h4452, h4576, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4578 | h4578
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4579 | h4579
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4580 | h4580
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4581 | h4581
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4582 | h4582
                        · linarith only [h4574, h4582, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4584 | h4584
                          · linarith only [h3977, h4576, h4584, hc01, hlam, hphi, u0ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4586 | h4586
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4587 | h4587
                              · linarith only [h3977, h4452, h4579, h4582, h4586, h4587, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4589 | h4589
                                · linarith only [h3977, h4452, h4579, h4584, h4589, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4591 | h4591
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4592 | h4592
                                    · rcases h2bigk with h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c | h4593c
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h0, hlam, p4593_1]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        rcases p4593_3 (m.d 0 2) (by simp) with h4596 | h4596
                                        · rcases p4593_3 (m.d 1 2) (by simp) with h4597 | h4597
                                          · rcases p4593_3 (m.d 2 3) (by simp) with h4598 | h4598
                                            · linarith only [h4598, hlam, p4593_0]
                                            · rcases p4593_3 (m.d 2 4) (by simp) with h4600 | h4600
                                              · linarith only [h4572, h4600, hlam]
                                              · linarith only [h4587, h4600, hlam]
                                          · linarith only [h4579, h4597, hlam]
                                        · linarith only [h4596, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h0, h4591, hc12, hlam, hphi, ht01, ht0b, ht5b, p4593_1, u5ehi4]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        rcases p4593_3 (m.d 0 2) (by simp) with h4606 | h4606
                                        · rcases p4593_3 (m.d 1 2) (by simp) with h4607 | h4607
                                          · rcases p4593_3 (m.d 2 3) (by simp) with h4608 | h4608
                                            · linarith only [h4571, h4608, hlam]
                                            · rcases p4593_3 (m.d 2 4) (by simp) with h4610 | h4610
                                              · linarith only [h4572, h4610, hlam]
                                              · linarith only [h4591, h4610, hlam]
                                          · linarith only [h4581, h4607, hlam]
                                        · linarith only [h4606, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, p4593_1, u0ehi1]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        rcases p4593_3 (m.d 0 2) (by simp) with h4617 | h4617
                                        · linarith only [h0, h4617, hlam]
                                        · linarith only [h4571, h4617, hlam]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4591, hc12, hlam, hphi, ht01, ht0b, ht5b, p4593_1, u5ehi4]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        rcases p4593_3 (m.d 0 2) (by simp) with h4621 | h4621
                                        · linarith only [h0, h4621, hlam]
                                        · linarith only [h4573, h4621, hlam]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4571, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4579, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4587, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4589, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4572, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4580, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        rcases p4593_3 (m.d 0 2) (by simp) with h4631 | h4631
                                        · rcases p4593_3 (m.d 1 2) (by simp) with h4632 | h4632
                                          · rcases p4593_3 (m.d 2 3) (by simp) with h4633 | h4633
                                            · linarith only [h4587, h4633, hlam]
                                            · rcases p4593_3 (m.d 2 4) (by simp) with h4635 | h4635
                                              · rcases p4593_3 (m.d 2 5) (by simp) with h4636 | h4636
                                                · linarith only [h4591, h4636, hlam]
                                                · linarith only [h4589, h4636, hlam]
                                              · linarith only [h4587, h4635, hlam]
                                          · linarith only [h4579, h4632, hlam]
                                        · linarith only [h4571, h4631, hlam]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h0, h4572, h4591, hc12, hlam, hphi, ht01, ht0b, ht5b, p4593_1, u5ehi4]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4573, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4581, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        rcases p4593_3 (m.d 0 2) (by simp) with h4646 | h4646
                                        · rcases p4593_3 (m.d 1 2) (by simp) with h4647 | h4647
                                          · rcases p4593_3 (m.d 2 3) (by simp) with h4648 | h4648
                                            · linarith only [h4589, h4648, hlam]
                                            · rcases p4593_3 (m.d 2 4) (by simp) with h4650 | h4650
                                              · rcases p4593_3 (m.d 2 5) (by simp) with h4651 | h4651
                                                · rcases h3bigk with h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c | h4652c
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h3977, h4452, h4582, h4586, hc13, hc34, hlam, hphi, p4652_1]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h3977, h4452, h4582, h4586, hc23, hc34, hlam, hphi, p4652_1]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4574, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4576, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h3977, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h3977, h4452, h4582, h4586, hc23, hc34, hlam, hphi, p4652_1]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4582, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4584, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4571, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4579, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4587, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4589, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h0, h4572, h4591, hc12, hc23, hc34, hlam, hphi, ht01, p4593_1, p4652_1, u0ehi2]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    rcases p4652_3 (m.d 0 3) (by simp) with h4669 | h4669
                                                    · linarith only [h4574, h4669, hlam]
                                                    · linarith only [h3977, h4669, hlam]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    rcases p4652_3 (m.d 0 3) (by simp) with h4672 | h4672
                                                    · linarith only [h4574, h4672, hlam]
                                                    · linarith only [h4571, h4672, hlam]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h0, h4452, h4572, h4584, h4591, hc01, hc12, hc23, hc34, hlam, hphi, p4593_1, p4652_1]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h0, h4572, h4591, hc12, hc23, hc35, hlam, hphi, ht01, p4593_1, p4652_1, u0ehi2]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    rcases p4652_3 (m.d 0 3) (by simp) with h4678 | h4678
                                                    · linarith only [h4576, h4678, hlam]
                                                    · linarith only [h3977, h4678, hlam]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    rcases p4652_3 (m.d 0 3) (by simp) with h4681 | h4681
                                                    · linarith only [h4576, h4681, hlam]
                                                    · linarith only [h4571, h4681, hlam]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [h4592, hlam, p4652_0]
                                                  · have p4652_0 := h4652c.1
                                                    have p4652_1 := h4652c.2.1
                                                    have p4652_2 := h4652c.2.2.1
                                                    have p4652_3 := h4652c.2.2.2
                                                    linarith only [hlam, p4652_0]
                                                · linarith only [h4589, h4651, hlam]
                                              · linarith only [h4587, h4650, hlam]
                                          · linarith only [h4579, h4647, hlam]
                                        · linarith only [h4571, h4646, hlam]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [h4591, hlam, p4593_0]
                                      · have p4593_0 := h4593c.1
                                        have p4593_1 := h4593c.2.1
                                        have p4593_2 := h4593c.2.2.1
                                        have p4593_3 := h4593c.2.2.2
                                        linarith only [hlam, p4593_0]
                                    · linarith only [h3977, h3978, h4582, h4592, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4693 | h4693
                                    · rcases h2bigk with h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c | h4694c
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h0, hlam, p4694_1]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        rcases p4694_3 (m.d 0 2) (by simp) with h4697 | h4697
                                        · rcases p4694_3 (m.d 1 2) (by simp) with h4698 | h4698
                                          · rcases p4694_3 (m.d 2 3) (by simp) with h4699 | h4699
                                            · linarith only [h4699, hlam, p4694_0]
                                            · rcases p4694_3 (m.d 2 4) (by simp) with h4701 | h4701
                                              · linarith only [h4572, h4701, hlam]
                                              · linarith only [h4587, h4701, hlam]
                                          · linarith only [h4579, h4698, hlam]
                                        · linarith only [h4697, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        rcases p4694_3 (m.d 0 2) (by simp) with h4706 | h4706
                                        · rcases p4694_3 (m.d 1 2) (by simp) with h4707 | h4707
                                          · rcases p4694_3 (m.d 2 3) (by simp) with h4708 | h4708
                                            · linarith only [h4571, h4708, hlam]
                                            · rcases p4694_3 (m.d 2 4) (by simp) with h4710 | h4710
                                              · linarith only [h4710, hlam, p4694_0]
                                              · rcases p4694_3 (m.d 2 5) (by simp) with h4712 | h4712
                                                · linarith only [h4573, h4712, hlam]
                                                · linarith only [h4591, h4712, hlam]
                                          · linarith only [h4580, h4707, hlam]
                                        · linarith only [h4706, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        rcases p4694_3 (m.d 0 2) (by simp) with h4717 | h4717
                                        · rcases p4694_3 (m.d 1 2) (by simp) with h4718 | h4718
                                          · rcases p4694_3 (m.d 2 3) (by simp) with h4719 | h4719
                                            · linarith only [h4571, h4719, hlam]
                                            · rcases p4694_3 (m.d 2 4) (by simp) with h4721 | h4721
                                              · linarith only [h4572, h4721, hlam]
                                              · rcases p4694_3 (m.d 2 5) (by simp) with h4723 | h4723
                                                · linarith only [h4723, hlam, p4694_0]
                                                · rcases h3bigk with h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c | h4725c
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h3977, h4452, h4579, h4582, h4586, hc23, hc34, hlam, hphi, p4725_1]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h3977, h4452, h4582, h4586, hc23, hc34, hlam, hphi, p4725_1]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4574, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4576, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h3977, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h3977, h4452, h4582, h4586, hc23, hc34, hlam, hphi, p4725_1]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4582, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4584, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4571, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4579, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4587, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4589, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p4725_1, u0ehi2]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    rcases p4725_3 (m.d 0 3) (by simp) with h4742 | h4742
                                                    · linarith only [h4574, h4742, hlam]
                                                    · linarith only [h3977, h4742, hlam]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    rcases p4725_3 (m.d 0 3) (by simp) with h4745 | h4745
                                                    · linarith only [h4574, h4745, hlam]
                                                    · linarith only [h4571, h4745, hlam]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4576, hc34, hlam, hphi, ht01, ht12, ht23, p4725_1, u0ehi2]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p4725_1, u0ehi2]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    rcases p4725_3 (m.d 0 3) (by simp) with h4751 | h4751
                                                    · linarith only [h4576, h4751, hlam]
                                                    · linarith only [h3977, h4751, hlam]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    rcases p4725_3 (m.d 0 3) (by simp) with h4754 | h4754
                                                    · linarith only [h4576, h4754, hlam]
                                                    · linarith only [h4571, h4754, hlam]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [h4693, hlam, p4725_0]
                                                  · have p4725_0 := h4725c.1
                                                    have p4725_1 := h4725c.2.1
                                                    have p4725_2 := h4725c.2.2.1
                                                    have p4725_3 := h4725c.2.2.2
                                                    linarith only [hlam, p4725_0]
                                          · linarith only [h4581, h4718, hlam]
                                        · linarith only [h4717, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, p4694_1, u0ehi1]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        rcases p4694_3 (m.d 0 2) (by simp) with h4763 | h4763
                                        · linarith only [h0, h4763, hlam]
                                        · linarith only [h4571, h4763, hlam]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        rcases p4694_3 (m.d 0 2) (by simp) with h4766 | h4766
                                        · linarith only [h0, h4766, hlam]
                                        · linarith only [h4572, h4766, hlam]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        rcases p4694_3 (m.d 0 2) (by simp) with h4769 | h4769
                                        · linarith only [h0, h4769, hlam]
                                        · linarith only [h4573, h4769, hlam]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4571, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4579, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4587, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4589, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4572, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4580, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h3978, h4578, h4582, h4591, hc23, hc34, hlam, hphi, p4694_1]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4591, hlam, p4694_1]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4573, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h4581, hlam, p4694_0]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h3978, h4578, h4582, h4591, hc23, hc34, hlam, hphi, p4694_1]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [h3978, h4578, h4582, h4587, h4591, hc23, hc34, hlam, hphi, p4694_1]
                                      · have p4694_0 := h4694c.1
                                        have p4694_1 := h4694c.2.1
                                        have p4694_2 := h4694c.2.2.1
                                        have p4694_3 := h4694c.2.2.2
                                        linarith only [hlam, p4694_0]
                                    · linarith only [h3978, h4578, h4582, h4693, hlam]
                            · linarith only [h3978, h4578, h4586, hlam]
                      · linarith only [h0, h4581, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                    · linarith only [h0, h4580, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h3977, h4579, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4792 | h4792
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4793 | h4793
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4794 | h4794
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4795 | h4795
                        · linarith only [h3977, h3978, h4578, h4795, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4797 | h4797
                          · linarith only [h3977, h3978, h4578, h4797, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4799 | h4799
                            · linarith only [h3977, h3978, h4578, h4795, h4799, hc13, hc34, hlam, hphi]
                            · linarith only [h3977, h3978, h4799, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                      · linarith only [h0, h3977, h4794, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h0, h4572, h4793, hlam]
                  · linarith only [h0, h3977, h4792, hc23, hlam, hphi, ht01, ht12, u0ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4805 | h4805
            · linarith only [h3977, h3978, h4805, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4807 | h4807
              · linarith only [h0, h3977, h4573, h4807, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4809 | h4809
                · linarith only [h4572, h4573, h4809, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4811 | h4811
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4812 | h4812
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4813 | h4813
                      · linarith only [h3978, h4572, h4573, h4813, hc12, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h0, h3977, h4813, hc25, hlam, hphi, ht01, ht12, u0ehi2]
                    · linarith only [h0, h3977, h4572, h4812, hc02, hlam, hphi, u0ehi2]
                  · linarith only [h0, h3977, h4811, hc23, hlam, hphi, ht01, ht12, u0ehi2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4818 | h4818
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4819 | h4819
            · linarith only [h0, h3977, h4572, h4819, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4821 | h4821
              · linarith only [h3977, h4452, h4821, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4823 | h4823
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4824 | h4824
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4825 | h4825
                    · linarith only [h4572, h4818, h4825, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h3977, h4825, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h3977, h4824, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · linarith only [h4572, h4818, h4823, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4830 | h4830
            · linarith only [h0, h3977, h4572, h4830, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4832 | h4832
              · linarith only [h0, h3977, h4818, h4832, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4834 | h4834
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4835 | h4835
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4836 | h4836
                    · linarith only [h0, h4572, h4836, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h3977, h4836, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h3977, h4835, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4840 | h4840
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4841 | h4841
                    · linarith only [h0, h3977, h4572, h4841, hc12, hlam, hphi, ht01, u0ehi2]
                    · linarith only [h0, h3977, h4841, hc24, hlam, hphi, ht01, ht12, u0ehi2]
                  · linarith only [h0, h3977, h4840, hc23, hlam, hphi, ht01, ht12, u0ehi2]
      · linarith only [h0, h3977, h4571, hlam]

end R2N4
