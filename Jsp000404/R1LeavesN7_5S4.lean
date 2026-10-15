import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S1
import Jsp000404.R1LeavesN7_5S2
import Jsp000404.R1LeavesN7_5S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3197 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h3313 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 1 2 3 (by decide) (by decide) with h4106 | h4106
  · linarith only [h0, h4, h4106, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4108 | h4108
    · linarith only [h0, h1304, h4108, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4110 | h4110
      · linarith only [h0, h1819, h4110, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4112 | h4112
        · linarith only [h1, h1947, h4, h4112, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4114 | h4114
          · linarith only [h1, h3197, h4114, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4116 | h4116
            · linarith only [h0, h1947, h2, h3313, h4, h4116, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4118 | h4118
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4119 | h4119
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4120 | h4120
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4121 | h4121
                    · linarith only [h0, h1947, h3313, h4, h4118, h4121, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1947, h4, h4120, h4121, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4124 | h4124
                    · linarith only [h0, h1304, h4120, h4124, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c | h4126c
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        rcases p4126_3 (m.d 0 1) (by simp) with h4128 | h4128
                        · rcases p4126_3 (m.d 0 2) (by simp) with h4129 | h4129
                          · linarith only [h0, h4129, hlam]
                          · rcases p4126_3 (m.d 0 3) (by simp) with h4131 | h4131
                            · linarith only [h1, h4131, hlam]
                            · linarith only [h4, h4131, hlam]
                        · linarith only [h0, h4128, hlam]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        rcases p4126_3 (m.d 0 1) (by simp) with h4135 | h4135
                        · rcases p4126_3 (m.d 0 2) (by simp) with h4136 | h4136
                          · linarith only [h0, h4136, hlam]
                          · rcases p4126_3 (m.d 0 3) (by simp) with h4138 | h4138
                            · linarith only [h1, h4138, hlam]
                            · rcases p4126_3 (m.d 0 4) (by simp) with h4140 | h4140
                              · linarith only [h2, h4140, hlam]
                              · linarith only [h1947, h4140, hlam]
                        · linarith only [h1, h4135, hlam]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        rcases p4126_3 (m.d 0 1) (by simp) with h4144 | h4144
                        · rcases p4126_3 (m.d 0 2) (by simp) with h4145 | h4145
                          · linarith only [h0, h4145, hlam]
                          · rcases p4126_3 (m.d 0 3) (by simp) with h4147 | h4147
                            · linarith only [h1, h4147, hlam]
                            · rcases p4126_3 (m.d 0 4) (by simp) with h4149 | h4149
                              · linarith only [h2, h4149, hlam]
                              · rcases p4126_3 (m.d 0 5) (by simp) with h4151 | h4151
                                · linarith only [h3, h4151, hlam]
                                · linarith only [h3313, h4151, hlam]
                        · linarith only [h2, h4144, hlam]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        rcases p4126_3 (m.d 0 1) (by simp) with h4155 | h4155
                        · rcases p4126_3 (m.d 0 2) (by simp) with h4156 | h4156
                          · linarith only [h0, h4156, hlam]
                          · rcases p4126_3 (m.d 0 3) (by simp) with h4158 | h4158
                            · linarith only [h1, h4158, hlam]
                            · rcases p4126_3 (m.d 0 4) (by simp) with h4160 | h4160
                              · linarith only [h2, h4160, hlam]
                              · rcases p4126_3 (m.d 0 5) (by simp) with h4162 | h4162
                                · linarith only [h3, h4162, hlam]
                                · rcases h0emin with h4164 | h4164 | h4164 | h4164 | h4164
                                  · rcases h1bigk with h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c | h4165c
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      rcases p4165_3 (m.d 0 1) (by simp) with h4167 | h4167
                                      · rcases p4165_3 (m.d 1 2) (by simp) with h4168 | h4168
                                        · linarith only [h4168, hlam, p4165_0]
                                        · rcases p4165_3 (m.d 1 3) (by simp) with h4170 | h4170
                                          · linarith only [h1, h4170, hlam]
                                          · linarith only [h4106, h4170, hlam]
                                      · linarith only [h4167, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      rcases p4165_3 (m.d 0 1) (by simp) with h4174 | h4174
                                      · rcases p4165_3 (m.d 1 2) (by simp) with h4175 | h4175
                                        · linarith only [h0, h4175, hlam]
                                        · rcases p4165_3 (m.d 1 3) (by simp) with h4177 | h4177
                                          · linarith only [h4177, hlam, p4165_0]
                                          · rcases p4165_3 (m.d 1 4) (by simp) with h4179 | h4179
                                            · linarith only [h2, h4179, hlam]
                                            · linarith only [h4112, h4179, hlam]
                                      · linarith only [h4174, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      rcases p4165_3 (m.d 0 1) (by simp) with h4183 | h4183
                                      · rcases p4165_3 (m.d 1 2) (by simp) with h4184 | h4184
                                        · linarith only [h0, h4184, hlam]
                                        · rcases p4165_3 (m.d 1 3) (by simp) with h4186 | h4186
                                          · linarith only [h1, h4186, hlam]
                                          · rcases p4165_3 (m.d 1 4) (by simp) with h4188 | h4188
                                            · linarith only [h4188, hlam, p4165_0]
                                            · rcases p4165_3 (m.d 1 5) (by simp) with h4190 | h4190
                                              · linarith only [h3, h4190, hlam]
                                              · linarith only [h4116, h4190, hlam]
                                      · linarith only [h4183, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      rcases p4165_3 (m.d 0 1) (by simp) with h4194 | h4194
                                      · rcases p4165_3 (m.d 1 2) (by simp) with h4195 | h4195
                                        · linarith only [h0, h4195, hlam]
                                        · rcases p4165_3 (m.d 1 3) (by simp) with h4197 | h4197
                                          · linarith only [h1, h4197, hlam]
                                          · rcases p4165_3 (m.d 1 4) (by simp) with h4199 | h4199
                                            · linarith only [h2, h4199, hlam]
                                            · rcases p4165_3 (m.d 1 5) (by simp) with h4201 | h4201
                                              · linarith only [h4201, hlam, p4165_0]
                                              · rcases h3bigk with h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c | h4203c
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h1947, h3313, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4126_1, p4203_1, u0elo0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4, hlam, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h1947, hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h3197, hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h1, hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4106, hlam, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4112, hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4114, hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  rcases p4203_3 (m.d 0 3) (by simp) with h4214 | h4214
                                                  · linarith only [h4, h4214, hlam]
                                                  · rcases p4203_3 (m.d 1 3) (by simp) with h4216 | h4216
                                                    · linarith only [h4106, h4216, hlam]
                                                    · rcases p4203_3 (m.d 2 3) (by simp) with h4218 | h4218
                                                      · rcases p4203_3 (m.d 3 4) (by simp) with h4219 | h4219
                                                        · linarith only [h4118, h4219, hlam]
                                                        · linarith only [h1947, h4219, hlam]
                                                      · linarith only [h4, h4218, hlam]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  rcases p4203_3 (m.d 0 3) (by simp) with h4223 | h4223
                                                  · linarith only [h4, h4223, hlam]
                                                  · linarith only [h1, h4223, hlam]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h0, h1947, h4, hc12, hc23, hlam, hphi, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h0, h1947, h4, h4124, hc12, hc23, hlam, hphi, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h0, h4, h4118, h4120, hc12, hc45, hlam, hphi, ht23, ht34, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4106, h4118, h4120, hc12, hc45, hlam, hphi, ht23, ht34, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4118, hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4124, hlam, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h0, h4, h4119, hc12, hc23, hlam, hphi, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4106, h4119, hc12, hc23, hlam, hphi, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h4119, hlam, p4203_0]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [h0, h1947, h4, h4119, hc12, hc23, hlam, hphi, p4203_1]
                                                · have p4203_0 := h4203c.1
                                                  have p4203_1 := h4203c.2.1
                                                  have p4203_2 := h4203c.2.2.1
                                                  have p4203_3 := h4203c.2.2.2
                                                  linarith only [hlam, p4203_0]
                                      · linarith only [h4194, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h0, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h4106, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h4108, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h4110, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h1, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4165_1, u0elo0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h4112, hlam, p4165_1]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h4114, hlam, p4165_1]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h2, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4165_1, u0elo0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h2, h3313, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4126_1, p4165_1, u0elo0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h4116, hlam, p4165_1]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h3, hlam, p4165_0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4126_1, p4165_1, u0elo0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h3, h4106, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4126_1, p4165_1, u0elo0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p4126_1, p4165_1, u0elo0]
                                    · have p4165_0 := h4165c.1
                                      have p4165_1 := h4165c.2.1
                                      have p4165_2 := h4165c.2.2.1
                                      have p4165_3 := h4165c.2.2.2
                                      linarith only [hlam, p4165_0]
                                  · linarith only [h1304, h4120, h4164, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h1947, h3313, h4164, hlam, p4126_1, u0elo0]
                                  · linarith only [h3313, h4164, hlam, p4126_1, u0elo0]
                                  · linarith only [h4164, hlam, p4126_1, u0elo0]
                        · linarith only [h3, h4155, hlam]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h0, hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h4, hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h1304, hlam, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h1819, hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h1, hlam, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h0, h1947, hc12, hc34, hlam, hphi, ht23, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h1947, hlam, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h3197, hlam, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h2, hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h0, h1304, h4120, hc12, hc45, hlam, hphi, ht23, ht34, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h1304, h4120, hc03, hc45, hlam, hphi, ht34, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h3313, hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h3, hlam, p4126_0]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h0, h3197, h4119, hc12, hc23, hlam, hphi, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h1, h3197, h4106, h4119, hc12, hc23, hlam, hphi, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [h0, h1304, h3197, h4119, hc12, hc23, hlam, hphi, p4126_1]
                      · have p4126_0 := h4126c.1
                        have p4126_1 := h4126c.2.1
                        have p4126_2 := h4126c.2.2.1
                        have p4126_3 := h4126c.2.2.2
                        linarith only [hlam, p4126_0]
                · linarith only [h0, h1947, h4, h4118, h4119, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4286 | h4286
                · linarith only [h0, h3197, h4, h4118, h4286, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4288 | h4288
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4289 | h4289
                    · rcases h0bigk with h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        rcases p4290_3 (m.d 0 1) (by simp) with h4292 | h4292
                        · rcases p4290_3 (m.d 0 2) (by simp) with h4293 | h4293
                          · linarith only [h0, h4293, hlam]
                          · rcases p4290_3 (m.d 0 3) (by simp) with h4295 | h4295
                            · linarith only [h1, h4295, hlam]
                            · linarith only [h4, h4295, hlam]
                        · linarith only [h0, h4292, hlam]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        rcases p4290_3 (m.d 0 1) (by simp) with h4299 | h4299
                        · rcases p4290_3 (m.d 0 2) (by simp) with h4300 | h4300
                          · linarith only [h0, h4300, hlam]
                          · rcases p4290_3 (m.d 0 3) (by simp) with h4302 | h4302
                            · linarith only [h1, h4302, hlam]
                            · rcases p4290_3 (m.d 0 4) (by simp) with h4304 | h4304
                              · linarith only [h2, h4304, hlam]
                              · linarith only [h1947, h4304, hlam]
                        · linarith only [h1, h4299, hlam]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        rcases p4290_3 (m.d 0 1) (by simp) with h4308 | h4308
                        · rcases p4290_3 (m.d 0 2) (by simp) with h4309 | h4309
                          · linarith only [h0, h4309, hlam]
                          · rcases p4290_3 (m.d 0 3) (by simp) with h4311 | h4311
                            · linarith only [h1, h4311, hlam]
                            · rcases p4290_3 (m.d 0 4) (by simp) with h4313 | h4313
                              · linarith only [h2, h4313, hlam]
                              · rcases p4290_3 (m.d 0 5) (by simp) with h4315 | h4315
                                · linarith only [h3, h4315, hlam]
                                · linarith only [h3313, h4315, hlam]
                        · linarith only [h2, h4308, hlam]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        rcases p4290_3 (m.d 0 1) (by simp) with h4319 | h4319
                        · rcases p4290_3 (m.d 0 2) (by simp) with h4320 | h4320
                          · linarith only [h0, h4320, hlam]
                          · rcases p4290_3 (m.d 0 3) (by simp) with h4322 | h4322
                            · linarith only [h1, h4322, hlam]
                            · rcases p4290_3 (m.d 0 4) (by simp) with h4324 | h4324
                              · linarith only [h2, h4324, hlam]
                              · rcases p4290_3 (m.d 0 5) (by simp) with h4326 | h4326
                                · linarith only [h3, h4326, hlam]
                                · rcases h0emin with h4328 | h4328 | h4328 | h4328 | h4328
                                  · rcases h1bigk with h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c | h4329c
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      rcases p4329_3 (m.d 0 1) (by simp) with h4331 | h4331
                                      · rcases p4329_3 (m.d 1 2) (by simp) with h4332 | h4332
                                        · linarith only [h4332, hlam, p4329_0]
                                        · rcases p4329_3 (m.d 1 3) (by simp) with h4334 | h4334
                                          · linarith only [h1, h4334, hlam]
                                          · linarith only [h4106, h4334, hlam]
                                      · linarith only [h4331, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      rcases p4329_3 (m.d 0 1) (by simp) with h4338 | h4338
                                      · rcases p4329_3 (m.d 1 2) (by simp) with h4339 | h4339
                                        · linarith only [h0, h4339, hlam]
                                        · rcases p4329_3 (m.d 1 3) (by simp) with h4341 | h4341
                                          · linarith only [h4341, hlam, p4329_0]
                                          · rcases p4329_3 (m.d 1 4) (by simp) with h4343 | h4343
                                            · linarith only [h2, h4343, hlam]
                                            · linarith only [h4112, h4343, hlam]
                                      · linarith only [h4338, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      rcases p4329_3 (m.d 0 1) (by simp) with h4347 | h4347
                                      · rcases p4329_3 (m.d 1 2) (by simp) with h4348 | h4348
                                        · linarith only [h0, h4348, hlam]
                                        · rcases p4329_3 (m.d 1 3) (by simp) with h4350 | h4350
                                          · linarith only [h1, h4350, hlam]
                                          · rcases p4329_3 (m.d 1 4) (by simp) with h4352 | h4352
                                            · linarith only [h4352, hlam, p4329_0]
                                            · rcases p4329_3 (m.d 1 5) (by simp) with h4354 | h4354
                                              · linarith only [h3, h4354, hlam]
                                              · linarith only [h4116, h4354, hlam]
                                      · linarith only [h4347, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      rcases p4329_3 (m.d 0 1) (by simp) with h4358 | h4358
                                      · rcases p4329_3 (m.d 1 2) (by simp) with h4359 | h4359
                                        · linarith only [h0, h4359, hlam]
                                        · rcases p4329_3 (m.d 1 3) (by simp) with h4361 | h4361
                                          · linarith only [h1, h4361, hlam]
                                          · rcases p4329_3 (m.d 1 4) (by simp) with h4363 | h4363
                                            · linarith only [h2, h4363, hlam]
                                            · rcases p4329_3 (m.d 1 5) (by simp) with h4365 | h4365
                                              · linarith only [h4365, hlam, p4329_0]
                                              · rcases h3bigk with h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c | h4367c
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h1947, h3313, h4288, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4, hlam, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h1947, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h3197, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h1, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4106, hlam, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4112, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4114, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4286, h4289, hc03, hc34, hlam, hphi, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4286, h4289, hc13, hc34, hlam, hphi, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4118, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4286, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  rcases p4367_3 (m.d 0 3) (by simp) with h4383 | h4383
                                                  · linarith only [h4383, hlam, p4367_0]
                                                  · rcases p4367_3 (m.d 1 3) (by simp) with h4385 | h4385
                                                    · linarith only [h4112, h4385, hlam]
                                                    · rcases p4367_3 (m.d 2 3) (by simp) with h4387 | h4387
                                                      · linarith only [h4118, h4387, hlam]
                                                      · linarith only [h4, h4387, hlam]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  rcases p4367_3 (m.d 0 3) (by simp) with h4390 | h4390
                                                  · linarith only [h1947, h4390, hlam]
                                                  · linarith only [h1, h4390, hlam]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h3197, hc03, hc34, hlam, hphi, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  rcases p4367_3 (m.d 0 3) (by simp) with h4396 | h4396
                                                  · linarith only [h4396, hlam, p4367_0]
                                                  · rcases p4367_3 (m.d 1 3) (by simp) with h4398 | h4398
                                                    · linarith only [h4114, h4398, hlam]
                                                    · rcases p4367_3 (m.d 2 3) (by simp) with h4400 | h4400
                                                      · linarith only [h4286, h4400, hlam]
                                                      · linarith only [h4, h4400, hlam]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  rcases p4367_3 (m.d 0 3) (by simp) with h4403 | h4403
                                                  · linarith only [h3197, h4403, hlam]
                                                  · linarith only [h1, h4403, hlam]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p4367_1]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [h4289, hlam, p4367_0]
                                                · have p4367_0 := h4367c.1
                                                  have p4367_1 := h4367c.2.1
                                                  have p4367_2 := h4367c.2.2.1
                                                  have p4367_3 := h4367c.2.2.2
                                                  linarith only [hlam, p4367_0]
                                      · linarith only [h4358, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h0, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h4106, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h4108, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h4110, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h1, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4329_1, u0elo0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h4112, hlam, p4329_1]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h4114, hlam, p4329_1]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h2, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h2, h3313, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4290_1, p4329_1, u0elo0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h2, h3313, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4290_1, p4329_1, u0elo0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h4116, hlam, p4329_1]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h3, hlam, p4329_0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4290_1, p4329_1, u0elo0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h3, h4106, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4290_1, p4329_1, u0elo0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p4290_1, p4329_1, u0elo0]
                                    · have p4329_0 := h4329c.1
                                      have p4329_1 := h4329c.2.1
                                      have p4329_2 := h4329c.2.2.1
                                      have p4329_3 := h4329c.2.2.2
                                      linarith only [hlam, p4329_0]
                                  · linarith only [h1947, h3313, h4, h4328, hlam, p4290_1, u0elo0]
                                  · linarith only [h1947, h3313, h4328, hlam, p4290_1, u0elo0]
                                  · linarith only [h3313, h4328, hlam, p4290_1, u0elo0]
                                  · linarith only [h4328, hlam, p4290_1, u0elo0]
                        · linarith only [h3, h4319, hlam]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h0, hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h4, hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h1304, hlam, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h1819, hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h1, hlam, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h0, h1947, hc12, hc34, hlam, hphi, ht23, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h1947, hlam, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h3197, hlam, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h2, hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h0, h3313, h4118, h4288, hc12, hc34, hlam, hphi, ht23, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h3313, h4118, h4288, hc03, hc34, hlam, hphi, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h3313, hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h3, hlam, p4290_0]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h0, h3313, h4118, h4288, hc12, hc34, hlam, hphi, ht23, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h1, h3313, h4106, h4118, h4288, hc12, hc34, hlam, hphi, ht23, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [h0, h1304, h3313, h4118, h4288, hc12, hc34, hlam, hphi, ht23, p4290_1]
                      · have p4290_0 := h4290c.1
                        have p4290_1 := h4290c.2.1
                        have p4290_2 := h4290c.2.2.1
                        have p4290_3 := h4290c.2.2.2
                        linarith only [hlam, p4290_0]
                    · linarith only [h4118, h4288, h4289, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4456 | h4456
                    · linarith only [h0, h4, h4118, h4288, h4456, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h4, h4118, h4456, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h3197 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 0 4 5 (by decide) (by decide) with h3313 | h3313
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h3197 h3313
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h3197 h3313

set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1947 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 0 3 5 (by decide) (by decide) with h3197 | h3197
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h3197
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947 h3197

set_option maxHeartbeats 5024000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg1819 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  have h1819 := hg1819
  rcases m.htr 0 3 4 (by decide) (by decide) with h1947 | h1947
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg1304 hg1819 h1947

set_option maxHeartbeats 5280000 in
set_option maxHeartbeats 5280000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg1304 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h1304 := hg1304
  rcases m.htr 0 2 5 (by decide) (by decide) with h1819 | h1819
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1820 | h1820
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1821 | h1821
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1822 | h1822
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1823 | h1823
          · linarith only [h0, h1823, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1825 | h1825
            · linarith only [h0, h1304, h1825, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1827 | h1827
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1828 | h1828
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1829 | h1829
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1830 | h1830
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1831 | h1831
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1832 | h1832
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1833 | h1833
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1834 | h1834
                            · linarith only [h1, h1828, h1834, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h1830, h1834, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h1304, h1828, h1830, h1833, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1821, h1832, h4, hlam]
                      · linarith only [h1820, h1831, h4, hlam]
                    · linarith only [h1, h1820, h1822, h1825, h1827, h1830, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h1, h1821, h1828, h1829, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1, h1820, h1823, h1827, h1828, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h1304, h1819, h1827, hc12, hc24, hlam, hphi]
        · linarith only [h1304, h1819, h1822, hlam]
      · linarith only [h1304, h1819, h1820, h1821, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1846 | h1846
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1847 | h1847
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1848 | h1848
          · linarith only [h0, h1848, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1850 | h1850
            · linarith only [h0, h1304, h1850, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1852 | h1852
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1853 | h1853
                · linarith only [h1, h1820, h1853, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1855 | h1855
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1856 | h1856
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1857 | h1857
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1858 | h1858
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1859 | h1859
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1860 | h1860
                            · rcases h0bigk with h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c | h1861c
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h0, h1852, h1858, h1860, hc45, hlam, hphi, ht0b, ht5b, p1861_1, u0elo0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1, h1848, h1852, h1858, h1860, hc45, hlam, hphi, ht0b, ht5b, p1861_1, u0elo0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1848, h1852, h1853, h1858, h1860, h2, hc45, hlam, hphi, ht0b, ht5b, p1861_1, u0elo0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                rcases p1861_3 (m.d 0 1) (by simp) with h1866 | h1866
                                · rcases p1861_3 (m.d 0 2) (by simp) with h1867 | h1867
                                  · linarith only [h0, h1867, hlam]
                                  · linarith only [h1819, h1867, hlam]
                                · linarith only [h1866, h3, hlam]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h0, hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h4, hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1304, hlam, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1820, h1857, h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1, hlam, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1820, h1857, hc02, hc23, hlam, hphi, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1820, hlam, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1819, h1820, h1857, h1858, h1860, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h2, hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h0, h1852, h1858, h1860, hc45, hlam, hphi, ht0b, ht5b, p1861_1, u0elo3]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1, h1848, h1852, h1858, h1860, hc45, hlam, hphi, ht0b, ht5b, p1861_1, u0elo3]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                rcases p1861_3 (m.d 0 1) (by simp) with h1885 | h1885
                                · rcases p1861_3 (m.d 0 2) (by simp) with h1886 | h1886
                                  · linarith only [h1304, h1886, hlam]
                                  · linarith only [h1819, h1886, hlam]
                                · linarith only [h1885, h3, hlam]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h3, hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1819, hlam, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1846, hlam, p1861_0]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [h1847, hlam, p1861_1]
                              · have p1861_0 := h1861c.1
                                have p1861_1 := h1861c.2.1
                                have p1861_2 := h1861c.2.2.1
                                have p1861_3 := h1861c.2.2.2
                                linarith only [hlam, p1861_0]
                            · linarith only [h1820, h1847, h1860, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1820, h1848, h1852, h1853, h1856, h1857, h1858, h1859, h2, h3, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1846, h1858, h4, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1898 | h1898
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1899 | h1899
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1900 | h1900
                            · rcases h0bigk with h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c | h1901c
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h0, h1852, h1898, h1900, hc45, hlam, hphi, ht0b, ht5b, p1901_1, u0elo0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h0, h1852, h1898, h1900, h4, hc45, hlam, hphi, ht0b, ht5b, p1901_1, u0elo0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h0, h1820, h1852, h1898, h1900, h4, hc45, hlam, hphi, ht0b, ht5b, p1901_1, u0elo0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                rcases p1901_3 (m.d 0 1) (by simp) with h1906 | h1906
                                · rcases p1901_3 (m.d 0 2) (by simp) with h1907 | h1907
                                  · linarith only [h0, h1907, hlam]
                                  · linarith only [h1819, h1907, hlam]
                                · linarith only [h1906, h3, hlam]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h0, hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h4, hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h1304, hlam, p1901_1]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h1857, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1901_1]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h1, hlam, p1901_1]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h0, h1820, h1852, hc25, hlam, hphi, ht0b, ht5b, p1901_1, u0elo3]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h1820, hlam, p1901_1]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                rcases p1901_3 (m.d 0 1) (by simp) with h1920 | h1920
                                · rcases p1901_3 (m.d 0 2) (by simp) with h1921 | h1921
                                  · linarith only [h1921, h4, hlam]
                                  · linarith only [h1819, h1921, hlam]
                                · linarith only [h1920, h3, hlam]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h2, hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h0, h1852, h1898, h1900, h2, hc45, hlam, hphi, ht0b, ht5b, p1901_1, u0elo0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h0, h1852, h1898, h1900, h2, h4, hc45, hlam, hphi, ht0b, ht5b, p1901_1, u0elo0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                rcases p1901_3 (m.d 0 1) (by simp) with h1929 | h1929
                                · rcases p1901_3 (m.d 0 2) (by simp) with h1930 | h1930
                                  · linarith only [h1304, h1930, hlam]
                                  · linarith only [h1819, h1930, hlam]
                                · linarith only [h1929, h3, hlam]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h3, hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h1819, hlam, p1901_1]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h1846, hlam, p1901_0]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [h1847, hlam, p1901_1]
                              · have p1901_0 := h1901c.1
                                have p1901_1 := h1901c.2.1
                                have p1901_2 := h1901c.2.2.1
                                have p1901_3 := h1901c.2.2.2
                                linarith only [hlam, p1901_0]
                            · linarith only [h0, h1852, h1857, h1898, h1900, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h1304, h1852, h1856, h1898, h1899, h3, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h1846, h1898, h4, hlam]
                    · linarith only [h1847, h1853, h1855, h1856, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h1846, h1848, h1852, h1855, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
              · linarith only [h1819, h1820, h1852, h4, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1819, h1820, h1847, h4, hlam]
      · linarith only [h1819, h1846, h4, hlam]
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s6 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h1304 h1819

end R2N4
