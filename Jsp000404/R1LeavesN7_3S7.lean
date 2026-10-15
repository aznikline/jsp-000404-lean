import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11192000 in
set_option maxHeartbeats 11192000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h3976 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  rcases m.htr 1 2 4 (by decide) (by decide) with h3977 | h3977
  · rcases m.htr 1 2 5 (by decide) (by decide) with h3978 | h3978
    · rcases m.htr 1 3 4 (by decide) (by decide) with h3979 | h3979
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3980 | h3980
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3981 | h3981
          · linarith only [h2, h3981, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3983 | h3983
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3984 | h3984
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3985 | h3985
                · linarith only [h2, h3977, h3985, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3987 | h3987
                  · linarith only [h2, h3977, h3983, h3987, h9, hlam]
                  · rcases h1bigk with h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c | h3989c
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3976, h3984, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3989_1]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h3992 | h3992
                      · rcases p3989_3 (m.d 1 2) (by simp) with h3993 | h3993
                        · linarith only [h0, h3993, hlam]
                        · linarith only [h3976, h3993, hlam]
                      · linarith only [h3992, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h3997 | h3997
                      · rcases p3989_3 (m.d 1 2) (by simp) with h3998 | h3998
                        · linarith only [h0, h3998, hlam]
                        · linarith only [h3977, h3998, hlam]
                      · linarith only [h3997, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h4002 | h4002
                      · rcases p3989_3 (m.d 1 2) (by simp) with h4003 | h4003
                        · linarith only [h0, h4003, hlam]
                        · linarith only [h3978, h4003, hlam]
                      · linarith only [h4002, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h0, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h0, h3976, h3984, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3989_1]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h4010 | h4010
                      · rcases p3989_3 (m.d 1 2) (by simp) with h4011 | h4011
                        · rcases p3989_3 (m.d 1 3) (by simp) with h4012 | h4012
                          · linarith only [h3976, h4012, hlam]
                          · linarith only [h3979, h4012, hlam]
                        · linarith only [h3977, h4011, hlam]
                      · linarith only [h2, h4010, hlam]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h4017 | h4017
                      · rcases p3989_3 (m.d 1 2) (by simp) with h4018 | h4018
                        · rcases p3989_3 (m.d 1 3) (by simp) with h4019 | h4019
                          · linarith only [h3976, h4019, hlam]
                          · linarith only [h3980, h4019, hlam]
                        · linarith only [h3978, h4018, hlam]
                      · linarith only [h3, h4017, hlam]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h1, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3976, hlam, p3989_1]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h4027 | h4027
                      · rcases p3989_3 (m.d 1 2) (by simp) with h4028 | h4028
                        · rcases p3989_3 (m.d 1 3) (by simp) with h4029 | h4029
                          · rcases p3989_3 (m.d 1 4) (by simp) with h4030 | h4030
                            · linarith only [h3979, h4030, hlam]
                            · rcases p3989_3 (m.d 1 5) (by simp) with h4032 | h4032
                              · linarith only [h3980, h4032, hlam]
                              · linarith only [h3981, h4032, hlam]
                          · linarith only [h3979, h4029, hlam]
                        · linarith only [h3977, h4028, hlam]
                      · linarith only [h2, h4027, hlam]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h4038 | h4038
                      · rcases p3989_3 (m.d 1 2) (by simp) with h4039 | h4039
                        · rcases p3989_3 (m.d 1 3) (by simp) with h4040 | h4040
                          · rcases p3989_3 (m.d 1 4) (by simp) with h4041 | h4041
                            · linarith only [h3979, h4041, hlam]
                            · rcases p3989_3 (m.d 1 5) (by simp) with h4043 | h4043
                              · linarith only [h3980, h4043, hlam]
                              · rcases h3bigk with h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c | h4045c
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3989_1, p4045_1]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  rcases p4045_3 (m.d 0 3) (by simp) with h4048 | h4048
                                  · rcases p4045_3 (m.d 1 3) (by simp) with h4049 | h4049
                                    · linarith only [h1, h4049, hlam]
                                    · linarith only [h3976, h4049, hlam]
                                  · linarith only [h4, h4048, hlam]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  rcases p4045_3 (m.d 0 3) (by simp) with h4053 | h4053
                                  · rcases p4045_3 (m.d 1 3) (by simp) with h4054 | h4054
                                    · linarith only [h1, h4054, hlam]
                                    · linarith only [h3979, h4054, hlam]
                                  · linarith only [h4053, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  rcases p4045_3 (m.d 0 3) (by simp) with h4058 | h4058
                                  · rcases p4045_3 (m.d 1 3) (by simp) with h4059 | h4059
                                    · linarith only [h1, h4059, hlam]
                                    · linarith only [h3980, h4059, hlam]
                                  · linarith only [h4058, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h1, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h1, h3984, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4045_1]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  rcases p4045_3 (m.d 0 3) (by simp) with h4066 | h4066
                                  · rcases p4045_3 (m.d 1 3) (by simp) with h4067 | h4067
                                    · rcases p4045_3 (m.d 2 3) (by simp) with h4068 | h4068
                                      · linarith only [h3976, h4068, hlam]
                                      · linarith only [h3983, h4068, hlam]
                                    · linarith only [h4067, hlam, p4045_0]
                                  · linarith only [h4066, h7, hlam]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  rcases p4045_3 (m.d 0 3) (by simp) with h4073 | h4073
                                  · rcases p4045_3 (m.d 1 3) (by simp) with h4074 | h4074
                                    · rcases p4045_3 (m.d 2 3) (by simp) with h4075 | h4075
                                      · linarith only [h3976, h4075, hlam]
                                      · linarith only [h3984, h4075, hlam]
                                    · linarith only [h4074, hlam, p4045_0]
                                  · linarith only [h4073, h8, hlam]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h4, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h3976, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h0, h3976, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4045_1]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h0, h3976, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4045_1]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h7, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h3979, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h3983, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h3987, hlam, p4045_1]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h8, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h3980, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h3984, hlam, p4045_0]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [h0, h3978, h3984, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4045_1]
                                · have p4045_0 := h4045c.1
                                  have p4045_1 := h4045c.2.1
                                  have p4045_2 := h4045c.2.2.1
                                  have p4045_3 := h4045c.2.2.2
                                  linarith only [hlam, p4045_0]
                          · linarith only [h3980, h4040, hlam]
                        · linarith only [h3978, h4039, hlam]
                      · linarith only [h3, h4038, hlam]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h2, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3977, hlam, p3989_1]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3979, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3981, hlam, p3989_1]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3978, hlam, p3989_1]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [h3980, hlam, p3989_0]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      rcases p3989_3 (m.d 0 1) (by simp) with h4106 | h4106
                      · rcases p3989_3 (m.d 1 2) (by simp) with h4107 | h4107
                        · rcases p3989_3 (m.d 1 3) (by simp) with h4108 | h4108
                          · rcases p3989_3 (m.d 1 4) (by simp) with h4109 | h4109
                            · linarith only [h3981, h4109, hlam]
                            · rcases p3989_3 (m.d 1 5) (by simp) with h4111 | h4111
                              · rcases h3bigk with h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c | h4112c
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h0, h3977, h3980, h3983, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3989_1, p4112_1]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  rcases p4112_3 (m.d 0 3) (by simp) with h4115 | h4115
                                  · rcases p4112_3 (m.d 1 3) (by simp) with h4116 | h4116
                                    · linarith only [h1, h4116, hlam]
                                    · linarith only [h3976, h4116, hlam]
                                  · linarith only [h4, h4115, hlam]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  rcases p4112_3 (m.d 0 3) (by simp) with h4120 | h4120
                                  · rcases p4112_3 (m.d 1 3) (by simp) with h4121 | h4121
                                    · linarith only [h1, h4121, hlam]
                                    · linarith only [h3979, h4121, hlam]
                                  · linarith only [h4120, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  rcases p4112_3 (m.d 0 3) (by simp) with h4125 | h4125
                                  · rcases p4112_3 (m.d 1 3) (by simp) with h4126 | h4126
                                    · linarith only [h1, h4126, hlam]
                                    · linarith only [h3980, h4126, hlam]
                                  · linarith only [h4125, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h1, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h1, h3984, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4112_1]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  rcases p4112_3 (m.d 0 3) (by simp) with h4133 | h4133
                                  · rcases p4112_3 (m.d 1 3) (by simp) with h4134 | h4134
                                    · rcases p4112_3 (m.d 2 3) (by simp) with h4135 | h4135
                                      · linarith only [h3976, h4135, hlam]
                                      · linarith only [h3983, h4135, hlam]
                                    · linarith only [h4134, hlam, p4112_0]
                                  · linarith only [h4133, h7, hlam]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  rcases p4112_3 (m.d 0 3) (by simp) with h4140 | h4140
                                  · rcases p4112_3 (m.d 1 3) (by simp) with h4141 | h4141
                                    · rcases p4112_3 (m.d 2 3) (by simp) with h4142 | h4142
                                      · linarith only [h3976, h4142, hlam]
                                      · linarith only [h3984, h4142, hlam]
                                    · linarith only [h4141, hlam, p4112_0]
                                  · linarith only [h4140, h8, hlam]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h4, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h3976, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h0, h3976, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4112_1]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h0, h3976, h3987, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4112_1]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h7, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h3979, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h3983, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h3987, hlam, p4112_1]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h8, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h3980, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h3984, hlam, p4112_0]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [h0, h3976, h3980, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4112_1]
                                · have p4112_0 := h4112c.1
                                  have p4112_1 := h4112c.2.1
                                  have p4112_2 := h4112c.2.2.1
                                  have p4112_3 := h4112c.2.2.2
                                  linarith only [hlam, p4112_0]
                              · linarith only [h3981, h4111, hlam]
                          · linarith only [h3979, h4108, hlam]
                        · linarith only [h3977, h4107, hlam]
                      · linarith only [h2, h4106, hlam]
                    · have p3989_0 := h3989c.1
                      have p3989_1 := h3989c.2.1
                      have p3989_2 := h3989c.2.2.1
                      have p3989_3 := h3989c.2.2.2
                      linarith only [hlam, p3989_0]
              · linarith only [h0, h3976, h3980, h3983, h3984, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4168 | h4168
              · linarith only [h0, h3976, h3979, h3983, h4168, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4170 | h4170
                · linarith only [h4170, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4172 | h4172
                  · linarith only [h2, h3979, h4172, h9, hlam]
                  · rcases h1bigk with h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c | h4174c
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3976, h3979, h3983, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3979, h3983, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      rcases p4174_3 (m.d 0 1) (by simp) with h4178 | h4178
                      · rcases p4174_3 (m.d 1 2) (by simp) with h4179 | h4179
                        · linarith only [h0, h4179, hlam]
                        · linarith only [h3977, h4179, hlam]
                      · linarith only [h4178, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      rcases p4174_3 (m.d 0 1) (by simp) with h4183 | h4183
                      · rcases p4174_3 (m.d 1 2) (by simp) with h4184 | h4184
                        · linarith only [h0, h4184, hlam]
                        · linarith only [h3978, h4184, hlam]
                      · linarith only [h4183, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h0, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3980, h3983, h4172, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h0, h3979, h3983, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h0, h3980, h3983, h4172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h1, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3976, hlam, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h1, h3979, h3983, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h0, h3976, h3980, h3983, h4172, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h2, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3977, hlam, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3979, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3981, hlam, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3978, hlam, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3980, hlam, p4174_0]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [h3, h3979, h3983, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4174_1]
                    · have p4174_0 := h4174c.1
                      have p4174_1 := h4174c.2.1
                      have p4174_2 := h4174c.2.2.1
                      have p4174_3 := h4174c.2.2.2
                      linarith only [hlam, p4174_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4208 | h4208
          · linarith only [h2, h3979, h3980, h4208, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4210 | h4210
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4211 | h4211
              · linarith only [h3976, h3980, h4211, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4213 | h4213
                · linarith only [h3977, h3979, h3980, h4, h4213, h8, h9, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4215 | h4215
                  · linarith only [h3978, h3980, h4210, h4211, h4215, h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases h1bigk with h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3976, h4210, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      rcases p4217_3 (m.d 0 1) (by simp) with h4220 | h4220
                      · rcases p4217_3 (m.d 1 2) (by simp) with h4221 | h4221
                        · linarith only [h0, h4221, hlam]
                        · linarith only [h3976, h4221, hlam]
                      · linarith only [h4220, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      rcases p4217_3 (m.d 0 1) (by simp) with h4225 | h4225
                      · rcases p4217_3 (m.d 1 2) (by simp) with h4226 | h4226
                        · linarith only [h0, h4226, hlam]
                        · linarith only [h3977, h4226, hlam]
                      · linarith only [h4225, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      rcases p4217_3 (m.d 0 1) (by simp) with h4230 | h4230
                      · rcases p4217_3 (m.d 1 2) (by simp) with h4231 | h4231
                        · linarith only [h0, h4231, hlam]
                        · linarith only [h3978, h4231, hlam]
                      · linarith only [h4230, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h0, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h0, h3976, h4210, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      rcases p4217_3 (m.d 0 1) (by simp) with h4238 | h4238
                      · rcases p4217_3 (m.d 1 2) (by simp) with h4239 | h4239
                        · rcases p4217_3 (m.d 1 3) (by simp) with h4240 | h4240
                          · linarith only [h3976, h4240, hlam]
                          · linarith only [h3979, h4240, hlam]
                        · linarith only [h3977, h4239, hlam]
                      · linarith only [h2, h4238, hlam]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h0, h3976, h3980, h4210, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h1, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3976, hlam, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3980, h4, h8, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3980, hlam, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h2, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3977, hlam, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3979, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h4208, hlam, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3, hlam, p4217_0]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3978, hlam, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [h3, h3976, h4210, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      rcases p4217_3 (m.d 0 1) (by simp) with h4259 | h4259
                      · rcases p4217_3 (m.d 1 2) (by simp) with h4260 | h4260
                        · rcases p4217_3 (m.d 1 3) (by simp) with h4261 | h4261
                          · linarith only [h3980, h4261, hlam]
                          · linarith only [h3979, h4261, hlam]
                        · linarith only [h3977, h4260, hlam]
                      · linarith only [h2, h4259, hlam]
                    · have p4217_0 := h4217c.1
                      have p4217_1 := h4217c.2.1
                      have p4217_2 := h4217c.2.2.1
                      have p4217_3 := h4217c.2.2.2
                      linarith only [hlam, p4217_0]
            · linarith only [h0, h3979, h3980, h4, h4210, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4268 | h4268
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4269 | h4269
          · linarith only [h3979, h4268, h4269, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h3979, h4268, h4269, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4272 | h4272
          · linarith only [h2, h3979, h4272, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4274 | h4274
            · linarith only [h3976, h3979, h4274, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4276 | h4276
              · linarith only [h3976, h3979, h4268, h4272, h4276, h7, h9, hc14, hc45, hlam, hphi]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4278 | h4278
                · linarith only [h2, h3977, h4278, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4280 | h4280
                  · linarith only [h4280, h7, h9, hlam]
                  · rcases h1bigk with h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c | h4282c
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4284 | h4284
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4285 | h4285
                        · linarith only [h4285, hlam, p4282_0]
                        · rcases p4282_3 (m.d 1 3) (by simp) with h4287 | h4287
                          · linarith only [h1, h4287, hlam]
                          · rcases p4282_3 (m.d 1 4) (by simp) with h4289 | h4289
                            · linarith only [h2, h4289, hlam]
                            · rcases p4282_3 (m.d 1 5) (by simp) with h4291 | h4291
                              · linarith only [h3, h4291, hlam]
                              · rcases h3bigk with h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  rcases p4293_3 (m.d 0 3) (by simp) with h4295 | h4295
                                  · rcases p4293_3 (m.d 1 3) (by simp) with h4296 | h4296
                                    · linarith only [h1, h4296, hlam]
                                    · rcases p4293_3 (m.d 2 3) (by simp) with h4298 | h4298
                                      · linarith only [h4, h4298, hlam]
                                      · rcases p4293_3 (m.d 3 4) (by simp) with h4300 | h4300
                                        · linarith only [h4300, h7, hlam]
                                        · linarith only [h3979, h4300, hlam]
                                  · linarith only [h1, h4295, hlam]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  rcases p4293_3 (m.d 0 3) (by simp) with h4304 | h4304
                                  · rcases p4293_3 (m.d 1 3) (by simp) with h4305 | h4305
                                    · linarith only [h1, h4305, hlam]
                                    · linarith only [h3976, h4305, hlam]
                                  · linarith only [h4, h4304, hlam]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  rcases p4293_3 (m.d 0 3) (by simp) with h4309 | h4309
                                  · rcases p4293_3 (m.d 1 3) (by simp) with h4310 | h4310
                                    · linarith only [h1, h4310, hlam]
                                    · rcases p4293_3 (m.d 2 3) (by simp) with h4312 | h4312
                                      · linarith only [h4, h4312, hlam]
                                      · rcases p4293_3 (m.d 3 4) (by simp) with h4314 | h4314
                                        · linarith only [h4314, hlam, p4293_0]
                                        · rcases p4293_3 (m.d 3 5) (by simp) with h4316 | h4316
                                          · linarith only [h4316, h8, hlam]
                                          · linarith only [h4280, h4316, hlam]
                                  · linarith only [h4309, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  rcases p4293_3 (m.d 0 3) (by simp) with h4320 | h4320
                                  · rcases p4293_3 (m.d 1 3) (by simp) with h4321 | h4321
                                    · linarith only [h1, h4321, hlam]
                                    · rcases p4293_3 (m.d 2 3) (by simp) with h4323 | h4323
                                      · linarith only [h4, h4323, hlam]
                                      · rcases p4293_3 (m.d 3 4) (by simp) with h4325 | h4325
                                        · linarith only [h4325, h7, hlam]
                                        · rcases p4293_3 (m.d 3 5) (by simp) with h4327 | h4327
                                          · linarith only [h4327, hlam, p4293_0]
                                          · rcases h5bigk with h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [hlam, p4329_0]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h3979, h4272, h9, hc13, hc45, hlam, hphi, ht34, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4274, h4278, h9, hc23, hc45, hlam, hphi, ht34, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4280, h9, hc34, hc45, hlam, hphi, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h9, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h3, hlam, p4329_0]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [hlam, p4329_0]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h3, h4274, h4278, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4268, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4272, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h6, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h3978, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [hlam, p4329_0]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4276, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4278, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h8, hlam, p4329_0]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p4293_1, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h0, h4, h4274, h4278, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4293_1, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [hlam, p4329_0]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4280, hlam, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h3, h3978, h4274, h4278, hc23, hc45, hlam, hphi, ht34, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h3978, h4274, h4278, hc23, hc45, hlam, hphi, ht34, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h4274, h4278, hc23, hc45, hlam, hphi, ht34, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [h3976, h4268, hc23, hc45, hlam, hphi, ht34, p4329_1]
                                            · have p4329_0 := h4329c.1
                                              have p4329_1 := h4329c.2.1
                                              have p4329_2 := h4329c.2.2.1
                                              have p4329_3 := h4329c.2.2.2
                                              linarith only [hlam, p4329_0]
                                  · linarith only [h4320, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h1, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h3979, hc23, hc34, hlam, hphi, p4293_1]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h3979, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h4268, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h4, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h3976, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h4274, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h4276, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h7, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p4293_1]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p4293_1]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h4280, hlam, p4293_1]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h8, hlam, p4293_0]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  rcases p4293_3 (m.d 0 3) (by simp) with h4372 | h4372
                                  · rcases p4293_3 (m.d 1 3) (by simp) with h4373 | h4373
                                    · linarith only [h4373, hlam, p4293_0]
                                    · rcases p4293_3 (m.d 2 3) (by simp) with h4375 | h4375
                                      · linarith only [h4276, h4375, hlam]
                                      · rcases p4293_3 (m.d 3 4) (by simp) with h4377 | h4377
                                        · linarith only [h4280, h4377, hlam]
                                        · linarith only [h3979, h4377, hlam]
                                  · linarith only [h1, h4372, hlam]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  rcases p4293_3 (m.d 0 3) (by simp) with h4381 | h4381
                                  · rcases p4293_3 (m.d 1 3) (by simp) with h4382 | h4382
                                    · linarith only [h4268, h4382, hlam]
                                    · linarith only [h3976, h4382, hlam]
                                  · linarith only [h4, h4381, hlam]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [h0, h3976, h3979, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4293_1]
                                · have p4293_0 := h4293c.1
                                  have p4293_1 := h4293c.2.1
                                  have p4293_2 := h4293c.2.2.1
                                  have p4293_3 := h4293c.2.2.2
                                  linarith only [hlam, p4293_0]
                      · linarith only [h4284, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4389 | h4389
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4390 | h4390
                        · linarith only [h0, h4390, hlam]
                        · linarith only [h3976, h4390, hlam]
                      · linarith only [h4389, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4394 | h4394
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4395 | h4395
                        · linarith only [h0, h4395, hlam]
                        · linarith only [h3977, h4395, hlam]
                      · linarith only [h4394, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4399 | h4399
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4400 | h4400
                        · linarith only [h0, h4400, hlam]
                        · linarith only [h3978, h4400, hlam]
                      · linarith only [h4399, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h0, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4406 | h4406
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4407 | h4407
                        · rcases p4282_3 (m.d 1 3) (by simp) with h4408 | h4408
                          · linarith only [h3976, h4408, hlam]
                          · rcases p4282_3 (m.d 1 4) (by simp) with h4410 | h4410
                            · linarith only [h3977, h4410, hlam]
                            · linarith only [h3979, h4410, hlam]
                        · linarith only [h3976, h4407, hlam]
                      · linarith only [h1, h4406, hlam]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4415 | h4415
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4416 | h4416
                        · rcases p4282_3 (m.d 1 3) (by simp) with h4417 | h4417
                          · linarith only [h3976, h4417, hlam]
                          · rcases p4282_3 (m.d 1 4) (by simp) with h4419 | h4419
                            · linarith only [h3977, h4419, hlam]
                            · rcases p4282_3 (m.d 1 5) (by simp) with h4421 | h4421
                              · linarith only [h3978, h4421, hlam]
                              · linarith only [h4272, h4421, hlam]
                        · linarith only [h3977, h4416, hlam]
                      · linarith only [h2, h4415, hlam]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4426 | h4426
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4427 | h4427
                        · rcases p4282_3 (m.d 1 3) (by simp) with h4428 | h4428
                          · linarith only [h3976, h4428, hlam]
                          · rcases p4282_3 (m.d 1 4) (by simp) with h4430 | h4430
                            · linarith only [h3977, h4430, hlam]
                            · rcases p4282_3 (m.d 1 5) (by simp) with h4432 | h4432
                              · linarith only [h3978, h4432, hlam]
                              · rcases h3bigk with h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c | h4434c
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  rcases p4434_3 (m.d 0 3) (by simp) with h4436 | h4436
                                  · rcases p4434_3 (m.d 1 3) (by simp) with h4437 | h4437
                                    · linarith only [h1, h4437, hlam]
                                    · rcases p4434_3 (m.d 2 3) (by simp) with h4439 | h4439
                                      · linarith only [h4, h4439, hlam]
                                      · rcases p4434_3 (m.d 3 4) (by simp) with h4441 | h4441
                                        · linarith only [h4441, h7, hlam]
                                        · linarith only [h3979, h4441, hlam]
                                  · linarith only [h1, h4436, hlam]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  rcases p4434_3 (m.d 0 3) (by simp) with h4445 | h4445
                                  · rcases p4434_3 (m.d 1 3) (by simp) with h4446 | h4446
                                    · linarith only [h1, h4446, hlam]
                                    · linarith only [h3976, h4446, hlam]
                                  · linarith only [h4, h4445, hlam]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  rcases p4434_3 (m.d 0 3) (by simp) with h4450 | h4450
                                  · rcases p4434_3 (m.d 1 3) (by simp) with h4451 | h4451
                                    · linarith only [h1, h4451, hlam]
                                    · rcases p4434_3 (m.d 2 3) (by simp) with h4453 | h4453
                                      · linarith only [h4, h4453, hlam]
                                      · rcases p4434_3 (m.d 3 4) (by simp) with h4455 | h4455
                                        · linarith only [h4455, hlam, p4434_0]
                                        · rcases p4434_3 (m.d 3 5) (by simp) with h4457 | h4457
                                          · linarith only [h4457, h8, hlam]
                                          · linarith only [h4280, h4457, hlam]
                                  · linarith only [h4450, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  rcases p4434_3 (m.d 0 3) (by simp) with h4461 | h4461
                                  · rcases p4434_3 (m.d 1 3) (by simp) with h4462 | h4462
                                    · linarith only [h1, h4462, hlam]
                                    · rcases p4434_3 (m.d 2 3) (by simp) with h4464 | h4464
                                      · linarith only [h4, h4464, hlam]
                                      · rcases p4434_3 (m.d 3 4) (by simp) with h4466 | h4466
                                        · linarith only [h4466, h7, hlam]
                                        · rcases p4434_3 (m.d 3 5) (by simp) with h4468 | h4468
                                          · linarith only [h4468, hlam, p4434_0]
                                          · rcases h5bigk with h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c | h4470c
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [hlam, p4470_0]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4272, h9, hc14, hc45, hlam, hphi, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4274, h4278, h9, hc23, hc45, hlam, hphi, ht34, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h3976, h3979, h4280, h9, hc23, hc45, hlam, hphi, ht34, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h9, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h3, hlam, p4470_0]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [hlam, p4470_0]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h3, h4274, h4278, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4268, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4272, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h6, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h3978, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [hlam, p4470_0]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4276, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4278, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h8, hlam, p4470_0]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [hc03, hc15, hlam, hphi, ht0b, ht5b, p4434_1, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h0, h4, h4274, h4278, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4434_1, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [hlam, p4470_0]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4280, hlam, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h3, h3978, h4274, h4278, hc23, hc45, hlam, hphi, ht34, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h3978, h4274, h4278, hc23, hc45, hlam, hphi, ht34, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h4274, h4278, hc23, hc45, hlam, hphi, ht34, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [h3976, h4268, hc23, hc45, hlam, hphi, ht34, p4470_1]
                                            · have p4470_0 := h4470c.1
                                              have p4470_1 := h4470c.2.1
                                              have p4470_2 := h4470c.2.2.1
                                              have p4470_3 := h4470c.2.2.2
                                              linarith only [hlam, p4470_0]
                                  · linarith only [h4461, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h1, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h3979, hc23, hc34, hlam, hphi, p4434_1]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h3979, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h4268, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h4, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h3976, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h4274, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h4276, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h7, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p4434_1]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p4434_1]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h4280, hlam, p4434_1]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h8, hlam, p4434_0]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  rcases p4434_3 (m.d 0 3) (by simp) with h4513 | h4513
                                  · rcases p4434_3 (m.d 1 3) (by simp) with h4514 | h4514
                                    · linarith only [h4514, hlam, p4434_0]
                                    · rcases p4434_3 (m.d 2 3) (by simp) with h4516 | h4516
                                      · linarith only [h4276, h4516, hlam]
                                      · rcases p4434_3 (m.d 3 4) (by simp) with h4518 | h4518
                                        · linarith only [h4280, h4518, hlam]
                                        · linarith only [h3979, h4518, hlam]
                                  · linarith only [h1, h4513, hlam]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  rcases p4434_3 (m.d 0 3) (by simp) with h4522 | h4522
                                  · rcases p4434_3 (m.d 1 3) (by simp) with h4523 | h4523
                                    · linarith only [h4268, h4523, hlam]
                                    · linarith only [h3976, h4523, hlam]
                                  · linarith only [h4, h4522, hlam]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [h3976, h3979, hc23, hc35, hlam, hphi, p4434_1]
                                · have p4434_0 := h4434c.1
                                  have p4434_1 := h4434c.2.1
                                  have p4434_2 := h4434c.2.2.1
                                  have p4434_3 := h4434c.2.2.2
                                  linarith only [hlam, p4434_0]
                        · linarith only [h3978, h4427, hlam]
                      · linarith only [h3, h4426, hlam]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h1, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h3976, hlam, p4282_1]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h3979, hlam, p4282_1]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h4268, hlam, p4282_1]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h2, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h3977, hlam, p4282_1]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h2, h3976, h9, hc23, hc45, hlam, hphi, ht34, p4282_1]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h4272, hlam, p4282_1]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h3, hlam, p4282_0]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [h3978, hlam, p4282_1]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4543 | h4543
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4544 | h4544
                        · rcases p4282_3 (m.d 1 3) (by simp) with h4545 | h4545
                          · linarith only [h4268, h4545, hlam]
                          · rcases p4282_3 (m.d 1 4) (by simp) with h4547 | h4547
                            · linarith only [h4272, h4547, hlam]
                            · linarith only [h3979, h4547, hlam]
                        · linarith only [h3976, h4544, hlam]
                      · linarith only [h1, h4543, hlam]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      rcases p4282_3 (m.d 0 1) (by simp) with h4552 | h4552
                      · rcases p4282_3 (m.d 1 2) (by simp) with h4553 | h4553
                        · rcases p4282_3 (m.d 1 3) (by simp) with h4554 | h4554
                          · linarith only [h4268, h4554, hlam]
                          · rcases p4282_3 (m.d 1 4) (by simp) with h4556 | h4556
                            · linarith only [h4272, h4556, hlam]
                            · rcases p4282_3 (m.d 1 5) (by simp) with h4558 | h4558
                              · rcases h3bigk with h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c | h4559c
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h3979, h4268, h8, hlam, p4282_1, p4559_2]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h3977, h4268, h4274, h8, hlam, p4282_1, p4559_2]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  rcases p4559_3 (m.d 0 3) (by simp) with h4563 | h4563
                                  · rcases p4559_3 (m.d 1 3) (by simp) with h4564 | h4564
                                    · linarith only [h1, h4564, hlam]
                                    · rcases p4559_3 (m.d 2 3) (by simp) with h4566 | h4566
                                      · linarith only [h4, h4566, hlam]
                                      · rcases p4559_3 (m.d 3 4) (by simp) with h4568 | h4568
                                        · linarith only [h4568, hlam, p4559_0]
                                        · rcases p4559_3 (m.d 3 5) (by simp) with h4570 | h4570
                                          · linarith only [h4570, h8, hlam]
                                          · linarith only [h4280, h4570, hlam]
                                  · linarith only [h4563, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h0, h3979, h4, h4268, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4282_1, p4559_1]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h1, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h3979, hc23, hc34, hlam, hphi, p4559_1]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h3979, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h4268, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h4, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h3976, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h4274, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h4276, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h7, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p4559_1]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p4559_1]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h4280, hlam, p4559_1]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h8, hlam, p4559_0]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  rcases p4559_3 (m.d 0 3) (by simp) with h4591 | h4591
                                  · rcases p4559_3 (m.d 1 3) (by simp) with h4592 | h4592
                                    · linarith only [h4592, hlam, p4559_0]
                                    · rcases p4559_3 (m.d 2 3) (by simp) with h4594 | h4594
                                      · linarith only [h4276, h4594, hlam]
                                      · rcases p4559_3 (m.d 3 4) (by simp) with h4596 | h4596
                                        · linarith only [h4280, h4596, hlam]
                                        · linarith only [h3979, h4596, hlam]
                                  · linarith only [h1, h4591, hlam]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  rcases p4559_3 (m.d 0 3) (by simp) with h4600 | h4600
                                  · rcases p4559_3 (m.d 1 3) (by simp) with h4601 | h4601
                                    · linarith only [h4268, h4601, hlam]
                                    · linarith only [h3976, h4601, hlam]
                                  · linarith only [h4, h4600, hlam]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [h3976, h3979, hc23, hc35, hlam, hphi, p4559_1]
                                · have p4559_0 := h4559c.1
                                  have p4559_1 := h4559c.2.1
                                  have p4559_2 := h4559c.2.2.1
                                  have p4559_3 := h4559c.2.2.2
                                  linarith only [hlam, p4559_0]
                              · linarith only [h4272, h4558, hlam]
                        · linarith only [h3977, h4553, hlam]
                      · linarith only [h2, h4552, hlam]
                    · have p4282_0 := h4282c.1
                      have p4282_1 := h4282c.2.1
                      have p4282_2 := h4282c.2.2.1
                      have p4282_3 := h4282c.2.2.2
                      linarith only [hlam, p4282_0]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h4611 | h4611
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4612 | h4612
        · linarith only [h3976, h3978, h4612, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4614 | h4614
          · linarith only [h2, h4614, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4616 | h4616
            · linarith only [h3976, h3978, h4616, h6, h9, hc34, hc45, hlam, hphi]
            · linarith only [h0, h3976, h3978, h4611, h4616, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h4619 | h4619
        · linarith only [h3977, h3978, h4611, h4619, h7, h9, hc24, hc45, hlam, hphi]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4621 | h4621
          · linarith only [h2, h4611, h4621, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h4623 | h4623
            · linarith only [h3976, h4611, h4623, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h4625 | h4625
              · linarith only [h3977, h3978, h4619, h4623, h4625, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h4627 | h4627
                · linarith only [h3977, h3978, h4625, h4627, h8, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h4629 | h4629
                  · linarith only [h3977, h3978, h4623, h4625, h4629, h8, h9, hc23, hc34, hlam, hphi]
                  · rcases h1bigk with h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c | h4631c
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      rcases p4631_3 (m.d 0 1) (by simp) with h4633 | h4633
                      · rcases p4631_3 (m.d 1 2) (by simp) with h4634 | h4634
                        · linarith only [h4634, hlam, p4631_0]
                        · rcases p4631_3 (m.d 1 3) (by simp) with h4636 | h4636
                          · linarith only [h1, h4636, hlam]
                          · rcases p4631_3 (m.d 1 4) (by simp) with h4638 | h4638
                            · linarith only [h2, h4638, hlam]
                            · rcases p4631_3 (m.d 1 5) (by simp) with h4640 | h4640
                              · linarith only [h3, h4640, hlam]
                              · linarith only [h3978, h4640, hlam]
                      · linarith only [h4633, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      rcases p4631_3 (m.d 0 1) (by simp) with h4644 | h4644
                      · rcases p4631_3 (m.d 1 2) (by simp) with h4645 | h4645
                        · linarith only [h0, h4645, hlam]
                        · linarith only [h3976, h4645, hlam]
                      · linarith only [h4644, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      rcases p4631_3 (m.d 0 1) (by simp) with h4649 | h4649
                      · rcases p4631_3 (m.d 1 2) (by simp) with h4650 | h4650
                        · linarith only [h0, h4650, hlam]
                        · linarith only [h3977, h4650, hlam]
                      · linarith only [h4649, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      rcases p4631_3 (m.d 0 1) (by simp) with h4654 | h4654
                      · rcases p4631_3 (m.d 1 2) (by simp) with h4655 | h4655
                        · linarith only [h0, h4655, hlam]
                        · rcases p4631_3 (m.d 1 3) (by simp) with h4657 | h4657
                          · linarith only [h1, h4657, hlam]
                          · rcases p4631_3 (m.d 1 4) (by simp) with h4659 | h4659
                            · linarith only [h2, h4659, hlam]
                            · rcases p4631_3 (m.d 1 5) (by simp) with h4661 | h4661
                              · linarith only [h4661, hlam, p4631_0]
                              · rcases h3bigk with h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c | h4663c
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  rcases p4663_3 (m.d 0 3) (by simp) with h4665 | h4665
                                  · rcases p4663_3 (m.d 1 3) (by simp) with h4666 | h4666
                                    · linarith only [h1, h4666, hlam]
                                    · rcases p4663_3 (m.d 2 3) (by simp) with h4668 | h4668
                                      · linarith only [h4, h4668, hlam]
                                      · rcases p4663_3 (m.d 3 4) (by simp) with h4670 | h4670
                                        · linarith only [h4670, h7, hlam]
                                        · linarith only [h4611, h4670, hlam]
                                  · linarith only [h1, h4665, hlam]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h3977, h3978, h4623, h4625, h8, hlam, p4663_2]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  rcases p4663_3 (m.d 0 3) (by simp) with h4675 | h4675
                                  · rcases p4663_3 (m.d 1 3) (by simp) with h4676 | h4676
                                    · linarith only [h1, h4676, hlam]
                                    · rcases p4663_3 (m.d 2 3) (by simp) with h4678 | h4678
                                      · linarith only [h4, h4678, hlam]
                                      · rcases p4663_3 (m.d 3 4) (by simp) with h4680 | h4680
                                        · linarith only [h4680, hlam, p4663_0]
                                        · rcases p4663_3 (m.d 3 5) (by simp) with h4682 | h4682
                                          · linarith only [h4682, h8, hlam]
                                          · linarith only [h4629, h4682, hlam]
                                  · linarith only [h4675, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h3977, h3978, h4623, h4625, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4663_1]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h1, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h4611, hc23, hc34, hlam, hphi, p4663_1]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h4611, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h4619, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h4, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h3976, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h4623, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h4625, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h7, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h7, h9, hc13, hc45, hlam, hphi, ht34, p4663_1]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h7, h9, hc23, hc45, hlam, hphi, ht34, p4663_1]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h4629, hlam, p4663_1]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h8, hlam, p4663_0]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  rcases p4663_3 (m.d 0 3) (by simp) with h4703 | h4703
                                  · rcases p4663_3 (m.d 1 3) (by simp) with h4704 | h4704
                                    · linarith only [h4704, hlam, p4663_0]
                                    · rcases p4663_3 (m.d 2 3) (by simp) with h4706 | h4706
                                      · linarith only [h4625, h4706, hlam]
                                      · rcases p4663_3 (m.d 3 4) (by simp) with h4708 | h4708
                                        · linarith only [h4629, h4708, hlam]
                                        · linarith only [h4611, h4708, hlam]
                                  · linarith only [h1, h4703, hlam]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  rcases p4663_3 (m.d 0 3) (by simp) with h4712 | h4712
                                  · rcases p4663_3 (m.d 1 3) (by simp) with h4713 | h4713
                                    · linarith only [h4619, h4713, hlam]
                                    · linarith only [h3976, h4713, hlam]
                                  · linarith only [h4, h4712, hlam]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [h3976, h4611, hc23, hc35, hlam, hphi, p4663_1]
                                · have p4663_0 := h4663c.1
                                  have p4663_1 := h4663c.2.1
                                  have p4663_2 := h4663c.2.2.1
                                  have p4663_3 := h4663c.2.2.2
                                  linarith only [hlam, p4663_0]
                      · linarith only [h4654, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h0, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h0, h3976, h3978, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h0, h3978, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h3978, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h1, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h3976, hlam, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h4611, hlam, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h4619, hlam, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h2, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h3977, hlam, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h2, h3976, h9, hc23, hc45, hlam, hphi, ht34, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h4621, hlam, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h3, hlam, p4631_0]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [h3, h3976, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4631_1]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      rcases p4631_3 (m.d 0 1) (by simp) with h4737 | h4737
                      · rcases p4631_3 (m.d 1 2) (by simp) with h4738 | h4738
                        · linarith only [h3978, h4738, hlam]
                        · linarith only [h3976, h4738, hlam]
                      · linarith only [h1, h4737, hlam]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      rcases p4631_3 (m.d 0 1) (by simp) with h4742 | h4742
                      · rcases p4631_3 (m.d 1 2) (by simp) with h4743 | h4743
                        · linarith only [h3978, h4743, hlam]
                        · linarith only [h3977, h4743, hlam]
                      · linarith only [h2, h4742, hlam]
                    · have p4631_0 := h4631c.1
                      have p4631_1 := h4631c.2.1
                      have p4631_2 := h4631c.2.2.1
                      have p4631_3 := h4631c.2.2.2
                      linarith only [hlam, p4631_0]
  · linarith only [h3976, h3977, h5, h9, hc23, hc45, hlam, hphi, ht34]

end R2N4
